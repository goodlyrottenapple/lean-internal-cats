# lean-internal-cats

This is an implementation of internal categories in Lean using the math-lib libraries.


## Install instructions 
*These instructions were adapted from this [document](https://github.com/leanprover-community/mathlib/blob/master/docs/install/project.md)*

First, [install Lean](https://github.com/leanprover-community/mathlib/blob/master/README.md). Open a terminal.

* Go the the directory where you would like this package to live.

* Run `git clone https://github.com/goodlyrottenapple/lean-internal-cats.git`.

* This creates a directory named `lean-internal-cats`. Enter it
  with `cd lean-internal-cats`.

* Type `leanpkg configure` to get `leanpkg` ready for use in this project.

* Type `update-mathlib` to get mathlib ready for use in this project.

* Type `leanpkg build` to compile everything, this should only take a few seconds.

* launch VScode, either through your application menu or by typing
  `code`

* On the main screen, or in the File menu, click "Open folder" (just "Open" on a Mac), and
  choose the folder `lean-internal-cats` (*not* one of its subfolders).

* Using the file explorer on the left-hand side, explore everthing you want in
  `lean-internal-cats/src`
