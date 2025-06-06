// Copyright 2000-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
package com.intellij.openapi.externalSystem.service.project.manage;

import com.intellij.execution.configurations.ConfigurationType;
import com.intellij.openapi.externalSystem.ExternalSystemManager;
import com.intellij.openapi.externalSystem.importing.ImportSpecBuilder;
import com.intellij.openapi.externalSystem.model.DataNode;
import com.intellij.openapi.externalSystem.model.ExternalSystemException;
import com.intellij.openapi.externalSystem.model.ProjectKeys;
import com.intellij.openapi.externalSystem.model.project.ModuleData;
import com.intellij.openapi.externalSystem.model.project.ProjectData;
import com.intellij.openapi.externalSystem.model.task.ExternalSystemTaskId;
import com.intellij.openapi.externalSystem.model.task.ExternalSystemTaskNotificationListener;
import com.intellij.openapi.externalSystem.service.execution.AbstractExternalSystemTaskConfigurationType;
import com.intellij.openapi.externalSystem.service.project.ExternalSystemProjectResolver;
import com.intellij.openapi.externalSystem.task.ExternalSystemTaskManager;
import com.intellij.openapi.externalSystem.util.ExternalSystemApiUtil;
import com.intellij.openapi.externalSystem.util.ExternalSystemUtil;
import com.intellij.openapi.module.Module;
import com.intellij.openapi.module.ModuleManager;
import com.intellij.openapi.util.Key;
import com.intellij.openapi.util.KeyWithDefaultValue;
import com.intellij.openapi.util.registry.Registry;
import com.intellij.openapi.util.registry.RegistryValue;
import com.intellij.openapi.util.text.StringUtil;
import com.intellij.platform.externalSystem.testFramework.TestExternalProjectSettings;
import com.intellij.platform.externalSystem.testFramework.TestExternalSystemExecutionSettings;
import com.intellij.platform.externalSystem.testFramework.TestExternalSystemManager;
import com.intellij.task.ProjectTaskManager;
import com.intellij.task.ProjectTaskRunner;
import com.intellij.testFramework.*;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import org.jetbrains.concurrency.Promise;

import java.util.Collections;

import static com.intellij.openapi.externalSystem.service.project.manage.ExternalSystemTaskActivator.Phase.*;
import static com.intellij.openapi.externalSystem.util.ExternalSystemConstants.USE_IN_PROCESS_COMMUNICATION_REGISTRY_KEY_SUFFIX;
import static com.intellij.openapi.externalSystem.util.ExternalSystemOperationTestUtil.DEFAULT_SYNC_TIMEOUT_MS;
import static com.intellij.platform.externalSystem.testFramework.ExternalSystemTestUtil.TEST_EXTERNAL_SYSTEM_ID;

public class ExternalSystemTaskActivatorTest extends HeavyPlatformTestCase {
  private static final Key<StringBuilder> TASKS_TRACE = KeyWithDefaultValue.create("tasks trace", StringBuilder::new);
  private static final String TEST_MODULE_NAME = "MyModule";
  private RegistryValue registryValue;

  @Override
  public void setUp() throws Exception {
    edt(() -> super.setUp());

    ExtensionTestUtil.addExtensions(ExternalSystemManager.EP_NAME, Collections.singletonList(new MyTestExternalSystemManager()), getTestRootDisposable());
    ExtensionTestUtil.maskExtensions(ConfigurationType.CONFIGURATION_TYPE_EP, Collections.singletonList(new TestTaskConfigurationType()), getTestRootDisposable());
    ExtensionTestUtil.maskExtensions(ProjectTaskRunner.EP_NAME, Collections.emptyList(), getTestRootDisposable());

    registryValue = Registry.get(TEST_EXTERNAL_SYSTEM_ID.getId() + USE_IN_PROCESS_COMMUNICATION_REGISTRY_KEY_SUFFIX);
    registryValue.setValue(true);

    String projectPath = "/project/path";
    TestExternalProjectSettings projectSettings = new TestExternalProjectSettings();
    projectSettings.setExternalProjectPath(projectPath);
    ExternalSystemUtil.linkExternalProject(projectSettings, new ImportSpecBuilder(myProject, TEST_EXTERNAL_SYSTEM_ID));

    // Wait for the external system initialisation and scheduled project sync
    TestObservation.waitForConfiguration(myProject, DEFAULT_SYNC_TIMEOUT_MS);
    IndexingTestUtil.waitUntilIndexesAreReady(myProject);
  }

  @Override
  public void tearDown() throws Exception {
    if (registryValue != null) {
      registryValue.setValue(false);
      registryValue = null;
    }
    edt(() -> super.tearDown());
  }

  @Override
  protected boolean runInDispatchThread() {
    return false;
  }

  public void testBeforeAfterBuildTasks() {
    Module module = ModuleManager.getInstance(myProject).findModuleByName(TEST_MODULE_NAME);
    addTaskTrigger("beforeBuildTask1", BEFORE_COMPILE, module);
    addTaskTrigger("beforeBuildTask2", BEFORE_COMPILE, module);
    addTaskTrigger("afterBuildTask1", AFTER_COMPILE, module);
    addTaskTrigger("afterBuildTask2", AFTER_COMPILE, module);
    addTaskTrigger("beforeReBuildTask1", BEFORE_REBUILD, module);
    addTaskTrigger("beforeReBuildTask2", BEFORE_REBUILD, module);
    addTaskTrigger("afterReBuildTask1", AFTER_REBUILD, module);
    addTaskTrigger("afterReBuildTask2", AFTER_REBUILD, module);
    build(module);
    assertEquals("beforeBuildTask1,beforeBuildTask2,afterBuildTask1,afterBuildTask2", TASKS_TRACE.get(myProject).toString());

    TASKS_TRACE.get(myProject).setLength(0);
    rebuild(module);
    assertEquals("beforeReBuildTask1,beforeReBuildTask2,afterReBuildTask1,afterReBuildTask2", TASKS_TRACE.get(myProject).toString());
  }

  private void addTaskTrigger(String taskName, ExternalSystemTaskActivator.Phase phase, Module module) {
    String projectPath = ExternalSystemApiUtil.getExternalProjectPath(module);
    ExternalSystemTaskActivator taskActivator = ExternalProjectsManagerImpl.getInstance(myProject).getTaskActivator();
    taskActivator.addTask(new ExternalSystemTaskActivator.TaskActivationEntry(TEST_EXTERNAL_SYSTEM_ID, phase, projectPath, taskName));
  }

  private static void build(@NotNull Module module) {
    Promise<ProjectTaskManager.Result> promise = ProjectTaskManager.getInstance(module.getProject()).build(module);
    edt(() -> PlatformTestUtil.waitForPromise(promise));
  }

  private static void rebuild(@NotNull Module module) {
    Promise<ProjectTaskManager.Result> promise = ProjectTaskManager.getInstance(module.getProject()).rebuild(module);
    edt(() -> PlatformTestUtil.waitForPromise(promise));
  }

  private static final class TestTaskConfigurationType extends AbstractExternalSystemTaskConfigurationType {
    private TestTaskConfigurationType() {super(TEST_EXTERNAL_SYSTEM_ID);}

    @Override
    protected @NotNull String getConfigurationFactoryId() {
      return "Test_external_system_id";
    }
  }

  private final class MyTestExternalSystemManager extends TestExternalSystemManager {
    private MyTestExternalSystemManager() {super(ExternalSystemTaskActivatorTest.this.myProject);}

    @NotNull
    @Override
    public Class<? extends ExternalSystemProjectResolver<TestExternalSystemExecutionSettings>> getProjectResolverClass() {
      return TestProjectResolver.class;
    }

    @Override
    public @NotNull Class<? extends ExternalSystemTaskManager<TestExternalSystemExecutionSettings>> getTaskManagerClass() {
      return TestTaskManager.class;
    }
  }

  public static class TestProjectResolver implements ExternalSystemProjectResolver<TestExternalSystemExecutionSettings> {

    @Nullable
    @Override
    public DataNode<ProjectData> resolveProjectInfo(@NotNull ExternalSystemTaskId id,
                                                    @NotNull String projectPath,
                                                    boolean isPreviewMode,
                                                    @Nullable TestExternalSystemExecutionSettings settings,
                                                    @NotNull ExternalSystemTaskNotificationListener listener)
      throws ExternalSystemException, IllegalArgumentException, IllegalStateException {
      DataNode<ProjectData> projectDataDataNode = new DataNode<>(
        ProjectKeys.PROJECT, new ProjectData(TEST_EXTERNAL_SYSTEM_ID, "MyProject", "", projectPath), null);
      projectDataDataNode.createChild(
        ProjectKeys.MODULE, new ModuleData("my-module", TEST_EXTERNAL_SYSTEM_ID, "myModuleType", TEST_MODULE_NAME, "", projectPath));
      return projectDataDataNode;
    }

    @Override
    public boolean cancelTask(@NotNull ExternalSystemTaskId taskId, @NotNull ExternalSystemTaskNotificationListener listener) {
      return false;
    }
  }

  public static class TestTaskManager implements ExternalSystemTaskManager<TestExternalSystemExecutionSettings> {

    @Override
    public void executeTasks(
      @NotNull String projectPath,
      @NotNull ExternalSystemTaskId id,
      @NotNull TestExternalSystemExecutionSettings settings,
      @NotNull ExternalSystemTaskNotificationListener listener
    ) throws ExternalSystemException {
      StringBuilder builder = TASKS_TRACE.get(id.findProject());
      if (!builder.isEmpty()) {
        builder.append(",");
      }
      builder.append(StringUtil.join(settings.getTasks(), ","));
    }

    @Override
    public boolean cancelTask(
      @NotNull ExternalSystemTaskId id,
      @NotNull ExternalSystemTaskNotificationListener listener
    ) throws ExternalSystemException {
      return false;
    }
  }
}