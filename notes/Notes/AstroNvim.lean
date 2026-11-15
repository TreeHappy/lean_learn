import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "AstroNvim" =>
%%%
tag := "astro-nvim"
htmlSplit := .never
%%%

[AstroNvim](https://astronvim.com){index}[AstroNvim] is the Neovim distribution used for this workspace.
It bundles LSP support, completion, treesitter, fuzzy finding, formatting, and a plugin manager on top of ordinary Neovim.

AstroNvim v6 uses [Lazy.nvim](https://github.com/folke/lazy.nvim) for plugins.
The configuration is a normal Neovim configuration, which makes it easy to add project-specific behavior.

# Configuration files
%%%
tag := "astro-files"
%%%

The user configuration lives in `~/.config/nvim`:

: `init.lua`

  Bootstraps Lazy, prepends `~/.elan/bin` to `vim.env.PATH`, then loads the rest of the configuration.

: `lua/lazy_setup.lua`

  Tells Lazy where to find plugin specifications.

: `lua/community.lua`

  Imports AstroCommunity packs.
  This repository imports the Lua pack and no longer imports the Lean pack.

: `lua/plugins/`

  One file per plugin or feature.
  Every file returns a Lazy specification.

: `lua/policies/`

  Optional rules for LSP behavior.

AstroNvim ships sensible defaults.
The files in `lua/plugins/` are for additions and overrides, not for rebuilding the distribution from scratch.

# Adding a plugin
%%%
tag := "astro-plugin"
%%%

Create a file in `lua/plugins/` that returns a table.
For example, `lua/plugins/lean.lua` loads `lean.nvim` for Lean buffers and sets its configuration:

```
return {
  {
    "Julian/lean.nvim",
    ft = { "lean" },
    init = function()
      vim.g.lean_config = vim.tbl_deep_extend("force", vim.g.lean_config or {}, {
        mappings = true,
      })
    end,
  },
}
```

The `ft` field makes the plugin lazy: it loads the first time a Lean file is opened.
The `init` field runs before loading, which is required for plugins that read global variables instead of exposing `setup`.

# Community packs
%%%
tag := "astro-community"
%%%

AstroCommunity is a collection of ready-made plugin specifications.
A pack is imported from `lua/community.lua`:

```
{ import = "astrocommunity.pack.lua" },
```

Packs are convenient, but they assume the plugin follows the usual `setup(opts)` convention.
When a plugin does not, as with `lean.nvim`, it is clearer to write a small specification in `lua/plugins/` and drop the pack.

# LSP layer
%%%
tag := "astro-lsp"
%%%

AstroLSP manages language server configuration.
It installs LSP keymaps when a client attaches, so `gd`, `gr`, `K`, and the diagnostics commands work in every supported file type.

The Lean server is special because `lean.nvim` supplies its own client definition and infoview integration.
AstroLSP still contributes the generic keymaps, while `lean.nvim` handles Lean-specific commands and hover.

# Where the Lean integration lives
%%%
tag := "astro-lean"
%%%

 * `~/.config/nvim/init.lua` makes the elan toolchain visible.
 * `~/.config/nvim/lua/community.lua` no longer imports the Lean pack.
 * `~/.config/nvim/lua/plugins/lean.lua` sets `vim.g.lean_config`.

The details are in {ref "lean-nvim"}[lean.nvim].
