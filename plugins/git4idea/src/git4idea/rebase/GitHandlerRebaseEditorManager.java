// Copyright 2000-2023 JetBrains s.r.o. and contributors. Use of this source code is governed by the Apache 2.0 license.
package git4idea.rebase;

import com.intellij.execution.CommandLineUtil;
import com.intellij.openapi.Disposable;
import com.intellij.openapi.diagnostic.Logger;
import com.intellij.openapi.util.Disposer;
import com.intellij.platform.eel.EelApi;
import git4idea.GitUtil;
import git4idea.commands.GitHandler;
import git4idea.commands.GitScriptGenerator;
import git4idea.config.GitExecutable;
import git4idea.editor.GitRebaseEditorAppHandler;
import org.jetbrains.annotations.NotNull;

import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.util.UUID;

import static git4idea.commands.GitCommand.GIT_EDITOR_ENV;

public final class GitHandlerRebaseEditorManager implements AutoCloseable {
  private static final Logger LOG = Logger.getInstance(GitHandlerRebaseEditorManager.class);

  private final @NotNull GitHandler myHandler;
  private final @NotNull GitRebaseEditorHandler myEditorHandler;
  private final @NotNull GitRebaseEditorService myService;

  private final Disposable myDisposable = Disposer.newDisposable();

  /**
   * Configure handler with editor
   */
  public static @NotNull GitHandlerRebaseEditorManager prepareEditor(GitHandler h, @NotNull GitRebaseEditorHandler editorHandler) {
    GitHandlerRebaseEditorManager manager = new GitHandlerRebaseEditorManager(h, editorHandler);
    GitUtil.tryRunOrClose(manager, () -> {
      manager.prepareEditor();
    });
    return manager;
  }

  private GitHandlerRebaseEditorManager(@NotNull GitHandler handler, @NotNull GitRebaseEditorHandler editorHandler) {
    myHandler = handler;
    myEditorHandler = editorHandler;
    myService = GitRebaseEditorService.getInstance();
  }

  private void prepareEditor() {
    if (myHandler.containsCustomEnvironmentVariable(GIT_EDITOR_ENV)) return;
    try {
      GitExecutable executable = myHandler.getExecutable();
      UUID handlerId = myService.registerHandler(myEditorHandler, executable, myDisposable);

      int port = myService.getIdePort();
      String scriptPath;
      if (myHandler.getExecutable() instanceof GitExecutable.Eel) {
        EelApi eelApi = ((GitExecutable.Eel)myHandler.getExecutable()).getEel();
        Path scriptFile = myService.getCallbackScriptPath(eelApi, false, myDisposable);
        scriptPath = executable.convertFilePath(scriptFile);
      }
      else {
        File scriptFile = myService.getCallbackScriptPath(executable.getId(), new GitScriptGenerator(executable), false);
        scriptPath = executable.convertFilePath(scriptFile.toPath());
      }

      myHandler.addCustomEnvironmentVariable(GIT_EDITOR_ENV, CommandLineUtil.posixQuote(scriptPath));
      myHandler.addCustomEnvironmentVariable(GitRebaseEditorAppHandler.IJ_EDITOR_HANDLER_ENV, handlerId.toString());
      myHandler.addCustomEnvironmentVariable(GitRebaseEditorAppHandler.IJ_EDITOR_PORT_ENV, Integer.toString(port));
    }
    catch (IOException e) {
      LOG.warn(e);
    }
  }

  @Override
  public void close() {
    Disposer.dispose(myDisposable);
  }
}
