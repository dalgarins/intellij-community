// Copyright 2000-2023 JetBrains s.r.o. and contributors. Use of this source code is governed by the Apache 2.0 license.
package com.intellij.codeInsight.lookup;

import com.intellij.openapi.application.AccessToken;
import com.intellij.openapi.util.Iconable;
import com.intellij.openapi.util.ScalableIcon;
import com.intellij.openapi.util.registry.Registry;
import com.intellij.psi.PsiElement;
import com.intellij.psi.meta.PsiMetaData;
import com.intellij.psi.util.PsiUtilCore;
import com.intellij.ui.IconManager;
import com.intellij.ui.PlatformIcons;
import com.intellij.ui.SizedIcon;
import com.intellij.util.SlowOperations;
import org.jetbrains.annotations.Nullable;

import javax.swing.*;

public final class DefaultLookupItemRenderer extends LookupElementRenderer<LookupItem<?>>{
  public static final DefaultLookupItemRenderer INSTANCE = new DefaultLookupItemRenderer();

  @Override
  public void renderElement(LookupItem<?> item, LookupElementPresentation presentation) {
    presentation.setIcon(getRawIcon(item));

    presentation.setItemText(getName(item));
    presentation.setItemTextBold(item.getAttribute(LookupItem.HIGHLIGHTED_ATTR) != null);
    presentation.setTailText(getText2(item), item.getAttribute(LookupItem.TAIL_TEXT_SMALL_ATTR) != null);
    presentation.setTypeText(getText3(item), null);
  }

  public static @Nullable Icon getRawIcon(final LookupElement item) {
    Icon icon;
    try (AccessToken ignore = SlowOperations.knownIssue("IDEA-344670, 32126317")) {
      icon = _getRawIcon(item);
    }
    if (icon instanceof ScalableIcon scalableIcon) {
      icon = scalableIcon.scale(1f);
    }
    if (icon != null && icon.getIconHeight() > IconManager.getInstance().getPlatformIcon(PlatformIcons.Class).getIconHeight()) {
      return new SizedIcon(icon, icon.getIconWidth(), IconManager.getInstance().getPlatformIcon(PlatformIcons.Class).getIconHeight());
    }
    return icon;
  }

  private static @Nullable Icon _getRawIcon(LookupElement item) {
    if (item instanceof LookupItem<?> lookupItem) {
      Icon icon = (Icon)lookupItem.getAttribute(LookupItem.ICON_ATTR);
      if (icon != null) return icon;
    }

    Object o = item.getObject();

    if (o instanceof Iconable iconable && !(o instanceof PsiElement)) {
      return iconable.getIcon(Registry.is("ide.completion.show.visibility.icon") ? Iconable.ICON_FLAG_VISIBILITY : 0);
    }

    final PsiElement element = item.getPsiElement();
    if (element != null && element.isValid()) {
      return element.getIcon(Registry.is("ide.completion.show.visibility.icon") ? Iconable.ICON_FLAG_VISIBILITY : 0);
    }
    return null;
  }


  @SuppressWarnings("deprecation")
  private static @Nullable String getText3(LookupItem<?> item) {
    Object o = item.getObject();
    String text;
    if (o instanceof LookupValueWithUIHint hint) {
      text = hint.getTypeHint();
    }
    else {
      text = (String)item.getAttribute(LookupItem.TYPE_TEXT_ATTR);
    }
    return text;
  }

  private static String getText2(LookupItem<?> item) {
    return (String)item.getAttribute(LookupItem.TAIL_TEXT_ATTR);
  }

  @SuppressWarnings("deprecation")
  private static String getName(LookupItem<?> item){
    final String presentableText = item.getPresentableText();
    if (presentableText != null) return presentableText;
    final Object o = item.getObject();
    String name = null;
    if (o instanceof PsiElement element) {
      if (element.isValid()) {
        name = PsiUtilCore.getName(element);
      }
    }
    else if (o instanceof PsiMetaData metaData) {
      name = metaData.getName();
    }
    else if (o instanceof PresentableLookupValue lookupValue) {
      name = lookupValue.getPresentation();
    }
    else {
      name = String.valueOf(o);
    }
    if (name == null){
      name = "";
    }

    return name;
  }
}
