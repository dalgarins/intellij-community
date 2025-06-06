// Copyright 2000-2024 JetBrains s.r.o. and contributors. Use of this source code is governed by the Apache 2.0 license.
@file:Suppress("TestOnlyProblems", "ReplaceGetOrSet", "HardCodedStringLiteral")

package com.intellij.ide.plugins

import com.intellij.diagnostic.PluginException
import com.intellij.ide.AppLifecycleListener
import com.intellij.ide.impl.ProjectUtil
import com.intellij.ide.plugins.cl.PluginClassLoader
import com.intellij.notification.Notification
import com.intellij.notification.NotificationType
import com.intellij.openapi.actionSystem.ActionManager
import com.intellij.openapi.actionSystem.ActionPlaces
import com.intellij.openapi.actionSystem.ActionUpdateThread
import com.intellij.openapi.actionSystem.AnActionEvent
import com.intellij.openapi.application.ApplicationManager
import com.intellij.openapi.components.Service
import com.intellij.openapi.diagnostic.logger
import com.intellij.openapi.extensions.ExtensionNotApplicableException
import com.intellij.openapi.extensions.impl.ExtensionPointImpl
import com.intellij.openapi.module.ModuleManager
import com.intellij.openapi.progress.ProcessCanceledException
import com.intellij.openapi.project.DumbAwareAction
import com.intellij.openapi.project.Project
import com.intellij.platform.ide.progress.ModalTaskOwner
import com.intellij.platform.ide.progress.runWithModalProgressBlocking
import com.intellij.platform.util.progress.reportSequentialProgress
import com.intellij.psi.stubs.StubElementTypeHolderEP
import com.intellij.serviceContainer.ComponentManagerImpl
import com.intellij.serviceContainer.ComponentManagerImpl.Companion.createAllServices2
import com.intellij.serviceContainer.getComponentManagerImpl
import com.intellij.util.lang.CompoundRuntimeException
import io.github.classgraph.*
import java.awt.Component
import java.lang.reflect.Constructor
import kotlin.properties.Delegates.notNull

private class CreateAllServicesAndExtensionsAction : DumbAwareAction() {
  override fun actionPerformed(e: AnActionEvent) {
    val errors = createAllServicesAndExtensions2()
    if (errors.isNotEmpty()) {
      logger<ComponentManagerImpl>().error(CompoundRuntimeException(errors))
    }
    // some errors are not thrown but logged
    val message = (if (errors.isEmpty()) "No errors" else "${errors.size} errors were logged") + ". Check also that no logged errors."
    Notification("Error Report", "", message, NotificationType.INFORMATION).notify(null)
  }

  override fun getActionUpdateThread(): ActionUpdateThread = ActionUpdateThread.BGT
}

private fun checkLightServices(
  application: ComponentManagerImpl,
  project: ComponentManagerImpl?,
  errors: MutableList<Throwable>,
) {
  for (mainDescriptor in PluginManagerCore.getPluginSet().enabledPlugins) {
    // we don't check classloader for sub descriptors because url set is the same
    val pluginClassLoader = mainDescriptor.pluginClassLoader as? PluginClassLoader
                            ?: continue
    scanClassLoader(pluginClassLoader).use { scanResult ->
      for (classInfo in scanResult.getClassesWithAnnotation(Service::class.java.name)) {
        checkLightServices(classInfo, mainDescriptor, application, project) {
          val error = when (it) {
            is ProcessCanceledException -> throw it
            is PluginException -> it
            else -> PluginException("Cannot create ${classInfo.name}", it, mainDescriptor.pluginId)
          }

          errors.add(error)
        }
      }
    }
  }
}

private class CreateAllServicesAndExtensionsActivity : AppLifecycleListener {
  init {
    if (!ApplicationManager.getApplication().isInternal ||
        !java.lang.Boolean.getBoolean("ide.plugins.create.all.services.and.extensions")) {
      throw ExtensionNotApplicableException.create()
    }
  }

  override fun appStarted() {
    ApplicationManager.getApplication().invokeLater {
      performAction()
    }
  }
}

fun performAction() {
  val actionManager = ActionManager.getInstance()
  actionManager.tryToExecute(
    actionManager.getAction(ACTION_ID),
    null,
    object: Component() {},
    ActionPlaces.UNKNOWN,
    true,
  )
}

private fun createAllServicesAndExtensions2(): List<Throwable> {
  val errors = mutableListOf<Throwable>()
  runWithModalProgressBlocking(ModalTaskOwner.guess(), "Creating all services and extensions") {
    reportSequentialProgress { reporter ->
      val taskExecutor: (task: () -> Unit) -> Unit = { task ->
        try {
          task()
        }
        catch (e: ProcessCanceledException) {
          throw e
        }
        catch (e: Throwable) {
          errors.add(e)
        }
      }

      // check first
      checkExtensionPoint(StubElementTypeHolderEP.EP_NAME.point as ExtensionPointImpl<*>, taskExecutor)

      val application = ApplicationManager.getApplication().getComponentManagerImpl()
      reporter.indeterminateStep {
        checkContainer2(application, "app", taskExecutor)
      }

      val project = ProjectUtil.getOpenProjects().firstOrNull()?.getComponentManagerImpl()
      if (project != null) {
        reporter.indeterminateStep {
          checkContainer2(project, "project", taskExecutor)
        }
        val module = ModuleManager.getInstance(project as Project).modules.firstOrNull()?.getComponentManagerImpl()
        if (module != null) {
          reporter.indeterminateStep {
            checkContainer2(module, "module", taskExecutor)
          }
        }
      }
      reporter.indeterminateStep("Checking light services...")
      checkLightServices(application, project, errors)
    }
  }
  return errors
}

// external usage in [src/com/jetbrains/performancePlugin/commands/chain/generalCommandChain.kt]
const val ACTION_ID: String = "CreateAllServicesAndExtensions"

/**
 * If service instance is obtained on Event Dispatch Thread only, it may expect that its constructor is called on EDT as well, so we must
 * honor this in the action.
 */
@Suppress("ReplaceJavaStaticMethodWithKotlinAnalog")
private val servicesWhichRequireEdt = java.util.Set.of(
  "com.intellij.usageView.impl.UsageViewContentManagerImpl",
  "com.intellij.python.scientific.figures.PyPlotToolWindow",
  "com.intellij.analysis.pwa.analyser.PwaServiceImpl",
  "com.intellij.analysis.pwa.view.toolwindow.PwaProblemsViewImpl",
)

/**
 * If service instance is obtained under read action only, it may expect that its constructor is called with read access, so we must honor
 * this in the action.
 */
private val servicesWhichRequireReadAction = setOf(
  "org.jetbrains.plugins.grails.lang.gsp.psi.gsp.impl.gtag.GspTagDescriptorService",
  "com.intellij.database.psi.DbFindUsagesOptionsProvider",
  "com.jetbrains.python.findUsages.PyFindUsagesOptions",
)

private val extensionPointsWhichRequireReadAction = setOf(
  "com.intellij.favoritesListProvider",
  "com.intellij.postStartupActivity",
  "com.intellij.backgroundPostStartupActivity",
  "org.jetbrains.kotlin.defaultErrorMessages",
)

private suspend fun checkContainer2(
  container: ComponentManagerImpl,
  levelDescription: String?,
  taskExecutor: (task: () -> Unit) -> Unit,
) = reportSequentialProgress { reporter ->
  reporter.indeterminateStep("Checking ${levelDescription} services...") {
    createAllServices2(container, servicesWhichRequireEdt, servicesWhichRequireReadAction)
  }
  reporter.indeterminateStep("Checking ${levelDescription} extensions...") {
    checkExtensions(container, taskExecutor)
  }
}

private fun checkExtensions(
  container: ComponentManagerImpl,
  taskExecutor: (task: () -> Unit) -> Unit,
) {
  container.extensionArea.processExtensionPoints { extensionPoint ->
    if (extensionPoint.name in extensionPointsWhichRequireReadAction) {
      return@processExtensionPoints
    }
    checkExtensionPoint(extensionPoint, taskExecutor)
  }
}

private fun checkExtensionPoint(extensionPoint: ExtensionPointImpl<*>, taskExecutor: (task: () -> Unit) -> Unit) {
  var extensionClass: Class<out Any> by notNull()
  taskExecutor {
    extensionClass = extensionPoint.getExtensionClass()
  }

  extensionPoint.checkImplementations { extension ->
    taskExecutor {
      val extensionInstance: Any
      try {
        extensionInstance = (extension.createInstance(extensionPoint.componentManager) ?: return@taskExecutor)
      }
      catch (e: Exception) {
        throw PluginException("Failed to instantiate extension (extension=$extension, pointName=${extensionPoint.name})",
                              e, extension.pluginDescriptor.pluginId)
      }

      if (!extensionClass.isInstance(extensionInstance)) {
        throw PluginException("$extension does not implement $extensionClass", extension.pluginDescriptor.pluginId)
      }
    }
  }
}

private fun scanClassLoader(pluginClassLoader: PluginClassLoader): ScanResult {
  return ClassGraph()
    .enableAnnotationInfo()
    .ignoreParentClassLoaders()
    .overrideClassLoaders(pluginClassLoader)
    .scan()
}

private fun checkLightServices(
  classInfo: ClassInfo,
  mainDescriptor: IdeaPluginDescriptorImpl,
  application: ComponentManagerImpl,
  project: ComponentManagerImpl?,
  onThrowable: (Throwable) -> Unit,
) {
  try {
    val lightServiceClass = when (val className = classInfo.name) {
                              // wants EDT/read action in constructor
                              "org.jetbrains.plugins.grails.runner.GrailsConsole",
                              "com.jetbrains.rdserver.editors.MultiUserCaretSynchronizerProjectService",
                              "com.intellij.javascript.web.webTypes.nodejs.WebTypesNpmLoader" -> null
                              // not clear - from what classloader light service will be loaded in reality
                              else -> loadLightServiceClass(className, mainDescriptor)
                            } ?: return

    val (isAppLevel, isProjectLevel) = classInfo.getAnnotationInfo(Service::class.java.name)
                                         .parameterValues
                                         .find { it.name == "value" }
                                         ?.let { levelsByAnnotations(it) }
                                       ?: levelsByConstructors(lightServiceClass.declaredConstructors)

    val components = listOfNotNull(
      if (isAppLevel) application else null,
      if (isProjectLevel) project else null,
    )

    for (component in components) {
      try {
        component.getService(lightServiceClass)
      }
      catch (e: Throwable) {
        onThrowable(e)
      }
    }
  }
  catch (e: Throwable) {
    onThrowable(e)
  }
}

private data class Levels(
  val isAppLevel: Boolean,
  val isProjectLevel: Boolean,
)

private fun levelsByConstructors(constructors: Array<Constructor<*>>): Levels {
  return Levels(
    isAppLevel = constructors.any { it.parameterCount == 0 },
    isProjectLevel = constructors.any { constructor ->
      constructor.parameterCount == 1
      && constructor.parameterTypes.get(0) == Project::class.java
    },
  )
}

private fun levelsByAnnotations(annotationParameterValue: AnnotationParameterValue): Levels {
  fun hasLevel(level: Service.Level) =
    (annotationParameterValue.value as Array<*>).asSequence()
      .map { it as AnnotationEnumValue }
      .any { it.name == level.name }

  return Levels(
    isAppLevel = hasLevel(Service.Level.APP),
    isProjectLevel = hasLevel(Service.Level.PROJECT),
  )
}

private fun loadLightServiceClass(
  className: String,
  mainDescriptor: IdeaPluginDescriptorImpl,
): Class<*>? {
  fun loadClass(descriptor: IdeaPluginDescriptorImpl) =
    (descriptor.pluginClassLoader as? PluginClassLoader)?.loadClass(className, true)

  for (moduleItem in mainDescriptor.contentModules) {
    try {
      // module is not loaded - dependency is not provided
      return loadClass(moduleItem)
    }
    catch (_: PluginException) {
    }
    catch (_: ClassNotFoundException) {
    }
  }

  // ok, or no plugin dependencies at all, or all are disabled, resolve from main
  return loadClass(mainDescriptor)
}
