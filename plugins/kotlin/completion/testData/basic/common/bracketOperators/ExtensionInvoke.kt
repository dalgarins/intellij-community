// Copyright 2000-2022 JetBrains s.r.o. and contributors. Use of this source code is governed by the Apache 2.0 license.
package p

class C

operator fun C.invoke(p: Int): Int = 0

fun foo(c: C) {
    c.<caret>
}

// IGNORE_K1
// EXIST: { lookupString: "()", itemText: "()", tailText: "(p: Int) for C in p", typeText: "Int", attributes: "bold", icon: "Function"}
