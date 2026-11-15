import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Verso" =>
%%%
tag := "verso"
htmlSplit := .never
%%%

[Verso](https://verso.lean-lang.org){index}[Verso] is a framework for writing documentation in Lean.
A document is a Lean package: the prose is parsed, elaborated, cross-referenced, and rendered by Lean code.

Verso has several genres for different document shapes.
This manual uses the *Manual* genre, which provides parts, chapters, sections, numbered headings, a table of contents, cross-references, an index, and a glossary.

# Markup
%%%
tag := "verso-markup"
%%%

Verso markup resembles Markdown, but it is parsed as Lean syntax and is stricter.

: Headers

  A line beginning with `#` starts a section. Repeated `#` characters create deeper levels.

: Emphasis and bold

  Underscores produce emphasis and asterisks produce bold text.

: Lists

  An unordered list item starts with `*`, `-`, or `+` in the left margin.
  A description list item starts with a colon followed by the term.

: Code

  Inline code uses backticks. A fenced block uses three or more backticks and an optional language tag.

: Links

  A link is written as `[text](https://example.com)`.

: Metadata

  A `%%%` block after a header attaches metadata such as a stable tag.

: Commands

  A line containing only a name in curly braces invokes an extension, for example an include or an index.

A small section with metadata looks like this:

````
# Markup
%%%
tag := "verso-markup"
%%%

Some *bold* and _emphasized_ text, plus `inline code`.

```lean
#check Nat
```
````

The `tag` is the stable identifier used by cross-references.
Keeping it unchanged when a file is renamed preserves every link.

# Cross-references
%%%
tag := "verso-refs"
%%%

Reference another tagged part with its tag and a display text:

```
See {ref "lake"}[the Lake chapter].
```

Verso resolves the tag during traversal and fails the build if it is missing or duplicated.
This is the replacement for wiki-style links: the target is a tag, not a filename.

# Anchors and external code
%%%
tag := "verso-anchors"
%%%

The most important feature for this repository is external code.
A note can quote Lean source from the `lean/` package without copying it.

In the source file, surround the region with anchor comments:

```
-- ANCHOR: double
def double (n : Nat) : Nat := n + n
-- ANCHOR_END: double
```

In the note, point Verso at the code package and the module, then reference the anchor:

````
set_option verso.exampleProject "../lean"
set_option verso.exampleModule "Brane.Basic"

```anchor double
```
````

Verso builds the code package, extracts the highlighted declaration, and inserts it with correct syntax highlighting and hover information.
Because the text is loaded at build time, the note cannot silently disagree with the source. An {deftech}_anchor_ is simply a named region of a module.

The path in `verso.exampleProject` is relative to the notes package.
A block can override the module with `(module := "Brane.Other")`.

# Index and glossary
%%%
tag := "verso-index"
%%%

An index entry is written `{index}[term]`, optionally with a subterm.
A glossary term is introduced with `{deftech}_term_`, which also adds an index entry.
The index itself is rendered with `{theIndex}`.

The final chapter of this manual demonstrates the index.
Index entries elsewhere in the text feed into it automatically.

# Building
%%%
tag := "verso-building"
%%%

From `notes/`:

```
lake build          # check the document
lake exe notes      # render to _out/html-multi
lake exe verso-serve _out/html-multi
```

The generator accepts options such as `--output DIR`, `--depth N`, `--with-tex`, and `--with-html-single`.
The development server watches the sources and serves the rendered site, which is the fastest way to edit prose.

The executable is declared in `notes/lakefile.toml` as `[[lean_exe]]` with root module `Main`.
`Main.lean` calls `manualMain (%doc Notes)`, where `Notes` is the root part defined in `Notes.lean`.

# Adding a chapter
%%%
tag := "verso-chapter"
%%%

To add a note:

 * Create `notes/Notes/MyTopic.lean` with `#doc (Manual) "My Topic" =>` and a unique `tag`.
 * Import it in `notes/Notes.lean`.
 * Add `{include 0 Notes.MyTopic}` at the desired position.
 * If the chapter quotes code, set `verso.exampleProject` and `verso.exampleModule` locally.

Because chapters are ordinary Lean modules, the editor gives diagnostics and completion inside the markup as well.
