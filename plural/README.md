# Plural examples

This directory includes a set of Java examples to be verified with Plural.

Since Plural is a unmaintained plugin for Eclipse, you need to follow these instructions:

1. Download [Eclipse Juno](https://www.eclipse.org/downloads/packages/release/juno) (an old version from 2012);
1. Download [PlaidAnnotations' source](https://code.google.com/archive/p/plaidannotations/source/default/source);
1. Download [Crystal's source](https://code.google.com/archive/p/crystalsaf/source/default/source);
1. Download [Plural's source](https://code.google.com/archive/p/pluralism/source/default/source);
1. Execute `eclipse.exe` (from the downloaded folder in step 1) with Java 8 available in `PATH`;
1. Go to `Help > Install New Software...` (keep `Show only the latest versions of available software` and `Group items by category` unselected);
1. Go to `Add...` and then `Local...`;
1. Select the folder `PlaidAnnotations' downloaded source/trunk/PlaidAnnotationsUpdateSite` and then click `OK` and `OK`;
1. Select `PlaidAnnotations` version `1.1.5` and then follow the installation to the end;
1. Then install `Crystal` version `3.3.6` from folder `Crystal's downloaded source/trunk/EclipseUpdate` (similar as before);
1. Then install `Plural` version `1.1.5` from folder `Plural's downloaded source/trunk/PluralEclipseUpdate` (similar as before);
1. Go to `Help > Check for Updates` and update `Crystal` now to the latest version;
1. Create a new Java project and copy the source files to there;
1. Eclipse will report that it cannot find the package `edu.cmu.cs.plural.annot`. Click on the error and select `Fix project setup...` and then `Add Plaid Annotations`;
1. Finally, go to `Crystal > Run Crystal`.
