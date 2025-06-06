// Copyright 2000-2025 JetBrains s.r.o. and contributors. Use of this source code is governed by the Apache 2.0 license.
package com.intellij.util.diff

import org.jetbrains.annotations.ApiStatus

@ApiStatus.Internal
interface LCSBuilder {
  fun addEqual(length: Int)
  fun addChange(first: Int, second: Int)
}
