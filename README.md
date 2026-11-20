# brane

A Lean 4 workspace with the code and its research notebook kept in separate packages.

* `lean/` is the code package. It depends on Mathlib `v4.34.0`.
* `notes/` is a [Verso](https://verso.lean-lang.org) Manual that documents the setup, the language, the editor, and the project.
* Notes quote real declarations from `lean/` through Verso anchors, so prose and code cannot drift apart.

Both packages use Lean `v4.34.0` (the figure generator's [Vizagrams](https://github.com/arademaker/vizagrams) dependency pins this release; see `docs/figures.md`).

## Requirements

* [elan](https://github.com/leanprover/elan), which provides `lean` and `lake`
* Neovim with [AstroNvim](https://astronvim.com) (optional, for the editor workflow)
* `make` (optional)

`~/.elan/bin` is added to `PATH` in `~/.bashrc`, and Neovim prepends it to `vim.env.PATH` in `init.lua`.
Without that entry the Lean language server cannot start, because Neovim does not read shell startup files.

## Build

```console
make lean     # check the Lean sources
make notes    # render the manual to notes/_out/html-multi
make serve    # preview the manual at http://localhost:8000
```

The same commands without `make`:

```console
cd lean  && lake build
cd notes && lake exe notes
cd notes && lake exe verso-serve _out/html-multi
```

## Layout

```text
.
├── lean/
│   ├── Brane.lean            library root
│   ├── Brane/Basic.lean      definitions quoted in the notes
│   ├── Brane/Exercises.lean  the first exercises
│   ├── Brane/Playground.lean scratch space
│   └── lakefile.toml
├── notes/
│   ├── Notes.lean            manual root: metadata and chapter list
│   ├── Notes/*.lean          one module per chapter
│   ├── Main.lean             the `notes` executable
│   ├── interactive/          browser demos (plain HTML/JS)
│   └── lakefile.toml
├── Makefile
└── README.md
```

## Adding a note

1. Create `notes/Notes/MyTopic.lean`:

   ```lean
   import VersoManual

   open Verso.Genre Manual

   #doc (Manual) "My Topic" =>
   %%%
   tag := "my-topic"
   %%%

   Text goes here.
   ```

2. Import it in `notes/Notes.lean` and include it:

   ```lean
   import Notes.MyTopic
   ...
   {include 0 Notes.MyTopic}
   ```

3. Reference it from anywhere with `{ref "my-topic"}[My Topic]`.

The `tag` is the stable identifier. Keep it when renaming the file.

## Quoting code

Mark a region in `lean/` with anchors:

```lean
-- ANCHOR: double
def double (n : Nat) : Nat := n + n
-- ANCHOR_END: double
```

Then in a note:

````text
set_option verso.exampleProject "../lean"
set_option verso.exampleModule "Brane.Basic"

```anchor double
def double (n : Nat) : Nat := n + n
```
````

The block content must match the source; Verso reports a diff if it does not, which is what keeps the notes honest.

## Interactive viewer

`notes/interactive/surface.html` is a 3D first-person visualization of
`lean/Brane/DifferentialGeometry.lean` — open it directly in a browser (it
loads Three.js from a CDN; no build step).

Each arrow on the surface is the JS transliteration of a definition in
`Brane.DiffGeom`: the tangents (`tangentX`, `tangentY`), the cross-product
normal (`normal_eq`), the horizontal gradient (`gradient_eq`), and the
second-derivative vectors (`tangentXX/XY/YX/YY`). Press `L` for a panel
quoting the Lean lemmas the on-screen objects correspond to.

Controls: `↑`/`↓` walk forward/backward along the surface, `←`/`→` turn in
place, `T`/`N`/`G`/`S` toggle tangents/normal/gradient/second derivatives,
`W` wireframe, `O` orbit camera, `1..n` switch surface. New surfaces are one
entry in the `SURFACES` registry at the top of the file.

`web/index.html` is the GitHub Pages game: a colourful terrain with a rolling
marble. It has two modes, geodesic pinball and a physics-driven walk mode;
switch with `1`/`2`. The geometry, forces and rolling constraint used by both
modes are derived in [`docs/game-math.md`](docs/game-math.md).

## Editor

The Lean integration is a custom `~/.config/nvim/lua/plugins/lean.lua` because `lean.nvim` has no `setup()` and reads `vim.g.lean_config` instead.
The AstroCommunity Lean pack has been removed, since its `opts` were silently ignored.

In a Lean buffer:

* `,i` toggles the infoview
* `K` shows Lean hover information
* `,r` restarts the Lean server for the current file
* `:LeanGoal` shows the main goal
* `:LeanLineDiagnostics` shows diagnostics for the current line

See `notes/Notes/LeanNvim.lean` for the full list and the PATH diagnosis.
