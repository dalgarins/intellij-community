// Copyright 2000-2024 JetBrains s.r.o. and contributors. Use of this source code is governed by the Apache 2.0 license.
@file:Suppress("ReplacePutWithAssignment")

package com.intellij.ide.plugins

import com.intellij.openapi.application.PathManager
import com.intellij.openapi.diagnostic.Logger
import com.intellij.openapi.diagnostic.debug
import com.intellij.openapi.extensions.PluginId
import org.jetbrains.annotations.ApiStatus.Internal
import java.io.BufferedInputStream
import java.io.BufferedOutputStream
import java.io.DataInputStream
import java.io.DataOutputStream
import java.lang.ref.Reference
import java.lang.ref.SoftReference
import java.nio.file.Files
import java.nio.file.NoSuchFileException
import java.nio.file.Path
import java.nio.file.Paths

@Suppress("SSBasedInspection")
private val LOG: Logger
  get() = Logger.getInstance("#com.intellij.ide.plugins.PluginManager")

internal fun getUpdatedBrokenPluginFile(configDir: Path? = null): Path =
  (configDir ?: PathManager.getConfigDir()).resolve("updatedBrokenPlugins.db")

private var brokenPluginVersions: Reference<Map<PluginId, Set<String>>>? = null

@Internal
fun isBrokenPlugin(pluginId: PluginId, version: String?): Boolean {
  val set = getBrokenPluginVersions()[pluginId]
  return set != null && set.contains(version)
}

@Internal
fun isBrokenPlugin(descriptor: IdeaPluginDescriptor): Boolean {
  return isBrokenPlugin(descriptor.pluginId, descriptor.version)
}

internal fun getBrokenPluginVersions(): Map<PluginId, Set<String>> {
  if (PluginEnabler.HEADLESS.isIgnoredDisabledPlugins) {
    LOG.debug { "Broken plugins will not be loaded because 'Ignore disabled plugins' flag is set" }
    return emptyMap()
  }

  var result = brokenPluginVersions?.get()
  if (result == null) {
    result = readBrokenPluginFile()
    brokenPluginVersions = SoftReference(result)
    LOG.debug { "Broken plugins is loaded, state size=${result.size}" }
  }
  return result
}

@Internal
fun updateBrokenPlugins(brokenPlugins: Map<PluginId, Set<String>>) {
  brokenPluginVersions = SoftReference(brokenPlugins)
  LOG.debug { "Broken plugins state is updated, state size=${brokenPlugins.size}" }
  writeBrokenPlugins(brokenPlugins)
}

@Internal
fun writeBrokenPlugins(brokenPlugins: Map<PluginId, Set<String>>, configDir: Path? = null) {
  LOG.debug { "Rewriting cached broken plugins, new state size=${brokenPlugins.size}" }
  val updatedBrokenPluginFile = getUpdatedBrokenPluginFile(configDir)
  try {
    DataOutputStream(BufferedOutputStream(Files.newOutputStream(updatedBrokenPluginFile), 32_000)).use { out ->
      out.write(2)
      out.writeUTF(PluginManagerCore.buildNumber.asString())
      out.writeInt(brokenPlugins.size)
      for ((key, value) in brokenPlugins) {
        out.writeUTF(key.idString)
        out.writeShort(value.size)
        for (s in value) {
          out.writeUTF(s)
        }
      }
    }
    LOG.debug("Cached broken plugins file is rewritten successfully")
  }
  catch (e: NoSuchFileException) {
    LOG.debug(e) { "Failed to update broken plugins file, because it doesn't exist: $updatedBrokenPluginFile" }
  }
  catch (e: Exception) {
    LOG.error("Failed to write $updatedBrokenPluginFile", e)
  }
}

@Internal
fun dropInMemoryBrokenPluginsCache() {
  if (brokenPluginVersions != null) {
    LOG.info("Broken plugins will be reloaded from disk")
  }
  brokenPluginVersions = null
}

private fun readBrokenPluginFile(): Map<PluginId, Set<String>> {
  var result: Map<PluginId, Set<String>>? = null
  val updatedBrokenPluginFile = getUpdatedBrokenPluginFile()
  if (Files.exists(updatedBrokenPluginFile)) {
    result = tryReadBrokenPluginsFile(updatedBrokenPluginFile)
    if (result != null) {
      LOG.info("Using cached broken plugins file")
    }
  } else {
    LOG.debug { "Cached broken plugins file doesn't exist: $updatedBrokenPluginFile" }
  }
  if (result == null) {
    result = tryReadBrokenPluginsFile(Paths.get(PathManager.getBinPath(), "brokenPlugins.db"))
    if (result != null) {
      LOG.info("Using broken plugins file from IDE distribution")
    } else {
      LOG.debug("Broken plugins file from the IDE distribution was not loaded")
    }
  }
  return result ?: emptyMap()
}

private fun tryReadBrokenPluginsFile(brokenPluginsStorage: Path): Map<PluginId, Set<String>>? {
  LOG.debug { "Reading broken plugins file: $brokenPluginsStorage" }
  try {
    DataInputStream(BufferedInputStream(Files.newInputStream(brokenPluginsStorage), 32_000)).use { stream ->
      val version = stream.readUnsignedByte()
      if (version != 2) {
        LOG.info("Unsupported version of $brokenPluginsStorage(fileVersion=$version, supportedVersion=2)")
        return null
      }

      val buildNumber = stream.readUTF()
      if (buildNumber != PluginManagerCore.buildNumber.toString()) {
        LOG.info("Ignoring cached broken plugins file from an earlier IDE build ($buildNumber)")
        return null
      }

      val count = stream.readInt()
      val result = HashMap<PluginId, Set<String>>(count)
      for (i in 0 until count) {
        val pluginId = PluginId.getId(stream.readUTF())
        result.put(pluginId, HashSet<String>().also { r ->
          repeat(stream.readUnsignedShort()) {
            r.add(stream.readUTF())
          }
        })
      }
      LOG.debug { "Broken plugins file at $brokenPluginsStorage was read, state size=${result.size}, buildNumber=${buildNumber}" }
      return result
    }
  }
  catch (e: NoSuchFileException) {
    LOG.debug(e) { "Broken plugins file doesn't exist: $brokenPluginsStorage" }
  }
  catch (e: Exception) {
    LOG.warn("Failed to read $brokenPluginsStorage", e)
  }
  return null
}