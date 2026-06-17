/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import Physlib.Meta.TODO.Basic
/-!

## Overview

PhyslibAlpha is an extension of Physlib with a lighter review process.
We expect the file structure to match where possible that of Physlib.

The idea is that it sits between the high review standards of Physlib and
just allowing anything in the project.

The review standard is similar to that of the arXiv, with a "one-look" policy.
We will look at the code once, and if it looks good, we will merge it, assuming
it passes CI checks.

We will not promise to matain files in PhyslibAlpha, if they break, we will simply
record when they broke.

We will make an effort to move files which are used frequently from PhyslibAlpha to Physlib,
undertaking the more rigorous review process.

-/

@[expose] public section
