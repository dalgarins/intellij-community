// Copyright 2000-2025 JetBrains s.r.o. and contributors. Use of this source code is governed by the Apache 2.0 license.
package com.siyeh.ipp.shift;

import com.siyeh.ipp.IPPTestCase;

public class ReplaceShiftWithMultiplyIntentionTest extends IPPTestCase {

  public void testLeftShift() { doTest("Replace '<<' with '*'"); }
  public void testLongShift() { doTest("Replace '<<' with '*'"); }
  public void testLargeShift() { doTest("Replace '<<' with '*'"); }
  public void testLeftShiftAssign() { doTest("Replace '<<=' with '*='"); }
  public void testLongShiftAssign() { doTest("Replace '<<=' with '*='"); }
  public void testParentheses() { doTest("Replace '<<' with '*'"); }
  public void testRightShift() { doTest("Replace '>>' with '/'"); }

  @Override
  protected String getRelativePath() {
    return "shift/replace_shift_with_multiply";
  }
}
