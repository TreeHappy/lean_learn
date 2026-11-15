import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Reservoir" =>
%%%
tag := "reservoir"
htmlSplit := .never
%%%

[Reservoir](https://reservoir.lean-lang.org){index}[Reservoir] is the community package registry for Lean.
It indexes libraries that can be consumed with Lake, together with their versions, documentation, and compatible toolchains.

Reservoir complements Mathlib: Mathlib is the shared mathematical library, while Reservoir hosts smaller or more specialized packages.

# Finding a package
%%%
tag := "reservoir-finding"
%%%

Search the website for a package, then add the dependency shown on its page to your `lakefile.toml`.
A registry dependency looks like this:

```
[[require]]
name = "some-package"
scope = "author-or-org"
rev = "v1.2.3"
```

The `scope` field identifies the Reservoir namespace, and `rev` selects a release tag.
After editing the lakefile, run `lake update` to resolve and record the new dependency.

# Git dependencies
%%%
tag := "reservoir-git"
%%%

A package that is not in Reservoir, or a specific unreleased revision, can be required directly from Git:

```
[[require]]
name = "subverso"
git = "https://github.com/leanprover/subverso"
rev = "892d6dc520270b5fb8c1291dd1b131e8c16255ed"
```

This is how `lean/` pins the SubVerso revision that matches Verso `v4.35.0`.
A full commit hash is more reproducible than a branch name.

# Compatibility
%%%
tag := "reservoir-compatibility"
%%%

A package must be compatible with the Lean version selected by `lean-toolchain`.
Reservoir pages list supported versions; when in doubt, check the package's own `lean-toolchain` and its dependency constraints.

Mixing packages built for different Lean releases usually produces obscure import errors.
Keeping the toolchain pinned in both packages avoids that class of problem.
