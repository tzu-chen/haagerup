/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Lean

/-!
# Core types: nodes, edges, graphs

A *result graph* has one node per user-facing declaration of a project and one
edge per dependency between two of them.

## Edge orientation

An edge is stored as `src → tgt` and always reads "`src` **is used by** `tgt`",
so edges run lemma → theorem and results accumulate in the direction of the
arrows. This is the orientation of the LaTeX `proofgraph` package, and it is
fixed: traversal direction and drawing direction are independent, so a "what
does this theorem use" graph is *walked* backwards from the theorem while every
edge in it is still *drawn* lemma → theorem.

## Statement versus proof

Constants occurring in a declaration's type are statement dependencies;
constants occurring only in its value are proof dependencies. The LaTeX package
records a reference made in the statement of a result and one made in its proof
alike, as the same sort of edge; here the two are told apart, and computed from
the elaborated term rather than guessed from cross-references.
-/

open Lean

namespace ResultGraph

/-! ## Kinds -/

/-- The sort of constant a node stands for: a case split on `ConstantInfo`. -/
inductive Kind where
  /-- An `axiom`. -/
  | ax
  /-- A `def`, `abbrev` or `instance`. -/
  | defn
  /-- A `theorem`. -/
  | thm
  /-- An `opaque` definition. -/
  | opaq
  /-- One of the `Quot` primitives. -/
  | quot
  /-- A constructor of an inductive type. -/
  | ctor
  /-- A recursor. -/
  | recr
  /-- An `inductive` type or `structure`. -/
  | indt
  deriving DecidableEq, Inhabited, Repr

namespace Kind

/-- The name of a kind, as it appears in JSON output. -/
def toString : Kind → String
  | .ax => "axiom"
  | .defn => "def"
  | .thm => "thm"
  | .opaq => "opaque"
  | .quot => "quot"
  | .ctor => "ctor"
  | .recr => "rec"
  | .indt => "inductive"

instance : ToString Kind := ⟨Kind.toString⟩

/-- Parse a kind back from its JSON spelling. -/
def ofString? : String → Option Kind
  | "axiom" => some .ax
  | "def" => some .defn
  | "thm" => some .thm
  | "opaque" => some .opaq
  | "quot" => some .quot
  | "ctor" => some .ctor
  | "rec" => some .recr
  | "inductive" => some .indt
  | _ => none

/-- The kind of a constant. -/
def ofConstantInfo : ConstantInfo → Kind
  | .axiomInfo _ => .ax
  | .defnInfo _ => .defn
  | .thmInfo _ => .thm
  | .opaqueInfo _ => .opaq
  | .quotInfo _ => .quot
  | .ctorInfo _ => .ctor
  | .recInfo _ => .recr
  | .inductInfo _ => .indt

/-- Whether this kind of constant is a *result* rather than a construction.
Only theorems are; the spine mode keeps exactly these. -/
def isResult : Kind → Bool
  | .thm => true
  | _ => false

end Kind

/-! ## Ranks -/

/-- How prominent a result is, on the axis the LaTeX package styles nodes by.

Lean draws no distinction between a theorem, a proposition and a lemma —
everything is `theorem` — so the rank is recovered from documentation signals
instead (see `ResultGraph.Rank`), and may be overridden per declaration. -/
inductive Rank where
  /-- A headline result of the library: cited in the root module's docstring. -/
  | result
  /-- A notable result: cited in some module's docstring. -/
  | thm
  /-- Any other public theorem. -/
  | lem
  /-- Not a result at all: a definition, inductive or structure. -/
  | defn
  deriving DecidableEq, Inhabited, Repr

namespace Rank

/-- The name of a rank, using the LaTeX package's vocabulary. -/
def toString : Rank → String
  | .result => "result"
  | .thm => "theorem"
  | .lem => "lemma"
  | .defn => "def"

instance : ToString Rank := ⟨Rank.toString⟩

/-- Parse a rank from its name; accepts the LaTeX package's spellings. -/
def ofString? : String → Option Rank
  | "result" => some .result
  | "theorem" => some .thm
  | "lemma" => some .lem
  | "def" | "definition" => some .defn
  | _ => none

/-- Whether a rank marks a *terminal* result, one the caller graph stops at:
headline results are what everything else leads to. -/
def isTerminal : Rank → Bool
  | .result => true
  | _ => false

end Rank

/-! ## Nodes and edges -/

/-- A declaration of the project under analysis. -/
structure Node where
  /-- The declaration's full name; for a private declaration, its user-facing
  name, with the `_private` mangling stripped. -/
  name : Name
  /-- The module the declaration was declared in. -/
  module : Name
  /-- What sort of constant it is. -/
  kind : Kind
  /-- Prominence, for styling. -/
  rank : Rank := .lem
  /-- Whether the declaration is `private`. -/
  isPrivate : Bool := false
  /-- Whether the declaration is `unsafe` or `partial`. -/
  isUnsafe : Bool := false
  /-- Whether the declaration's own statement or proof contains `sorry`. -/
  hasSorry : Bool := false
  /-- Whether the declaration depends, through the project's own declarations,
  on something containing `sorry`. Implied by `hasSorry`. -/
  sorryTainted : Bool := false
  /-- Axioms the declaration uses directly, other than `propext`,
  `Classical.choice` and `Quot.sound`. -/
  customAxioms : Array Name := #[]
  /-- Whether the declaration depends, through the project's own declarations,
  on a custom axiom. Implied by `customAxioms` being non-empty. -/
  axiomTainted : Bool := false
  deriving Inhabited, Repr

/-- Whether a node should be drawn as unsound or unfinished. Verification status
rides on the node *border*, an axis the rank scheme leaves free, so the two
compose: one figure is both a result graph and a `sorry` dashboard. -/
def Node.isFlagged (n : Node) : Bool :=
  n.sorryTainted || n.axiomTainted

/-- Where a dependency was found. -/
inductive EdgeKind where
  /-- The dependency occurs in the dependent's type. -/
  | statement
  /-- The dependency occurs in the dependent's value but not in its type. -/
  | proof
  deriving DecidableEq, Inhabited, Repr

namespace EdgeKind

/-- The name of an edge kind, as it appears in JSON output. -/
def toString : EdgeKind → String
  | .statement => "statement"
  | .proof => "proof"

instance : ToString EdgeKind := ⟨EdgeKind.toString⟩

/-- Parse an edge kind from its name. -/
def ofString? : String → Option EdgeKind
  | "statement" => some .statement
  | "proof" => some .proof
  | _ => none

end EdgeKind

/-- A dependency, drawn `src → tgt` and read "`src` is used by `tgt`". -/
structure Edge where
  /-- The declaration depended on (the lemma). -/
  src : Name
  /-- The declaration depending on it (the theorem). -/
  tgt : Name
  /-- Whether the dependency is in `tgt`'s statement or only in its proof. -/
  kind : EdgeKind
  deriving Inhabited, Repr

/-- A whole result graph. Nodes and edges are kept sorted so that output is
reproducible: the environment's constant map has no meaningful order. -/
structure Graph where
  /-- The module prefixes the graph was extracted for. -/
  roots : Array Name := #[]
  /-- The declarations. -/
  nodes : Array Node := #[]
  /-- The dependencies among them. -/
  edges : Array Edge := #[]
  deriving Inhabited

/-! ## Indexing -/

/-- Adjacency and lookup tables derived from a `Graph`, built once and shared by
every neighbourhood query. -/
structure Index where
  /-- Node data by name. -/
  node : Std.HashMap Name Node
  /-- For each declaration, the declarations it uses. -/
  uses : Std.HashMap Name (Array Name)
  /-- For each declaration, the declarations that use it. -/
  usedBy : Std.HashMap Name (Array Name)
  /-- The kind of the edge between two declarations, keyed `(src, tgt)`. -/
  edgeKind : Std.HashMap (Name × Name) EdgeKind
  deriving Inhabited

namespace Index

/-- Build the index of a graph. -/
def ofGraph (g : Graph) : Index := Id.run do
  let mut node : Std.HashMap Name Node := Std.HashMap.emptyWithCapacity g.nodes.size
  for n in g.nodes do
    node := node.insert n.name n
  let mut uses : Std.HashMap Name (Array Name) := Std.HashMap.emptyWithCapacity g.nodes.size
  let mut usedBy : Std.HashMap Name (Array Name) := Std.HashMap.emptyWithCapacity g.nodes.size
  let mut edgeKind : Std.HashMap (Name × Name) EdgeKind :=
    Std.HashMap.emptyWithCapacity g.edges.size
  for e in g.edges do
    uses := uses.insert e.tgt ((uses.getD e.tgt #[]).push e.src)
    usedBy := usedBy.insert e.src ((usedBy.getD e.src #[]).push e.tgt)
    edgeKind := edgeKind.insert (e.src, e.tgt) e.kind
  return { node, uses, usedBy, edgeKind }

/-- The neighbours of `n` to follow when walking in direction `dir`, where
`dir = true` means "what does this use" and `dir = false` means "what uses
this". -/
def neighbours (idx : Index) (dir : Bool) (n : Name) : Array Name :=
  if dir then idx.uses.getD n #[] else idx.usedBy.getD n #[]

end Index

/-! ## Contraction -/

/-- Contract the graph onto the nodes `drawn` keeps, routing every path through
the others instead of cutting it: with `d` left out, `A → d → B` becomes `A → B`.

This is what makes leaving a declaration out an *editorial* act rather than a
falsification. A private helper, a companion the elaborator generated, an
excluded namespace, a definition spine mode contracts away: each is a step of the
argument, and what its users reach through it does not stop being a dependency
because the step is not drawn. Cut the edges instead and a result whose whole
proof went through such a step comes out with nothing above it, a component
detached from the graph it belongs to.

A contracted edge counts as a statement dependency only if every step of the path
it stands for was one: a statement reached through a proof is something the proof
depends on, not something the statement mentions. -/
def Graph.contract (g : Graph) (drawn : Name → Bool) : Graph := Id.run do
  let idx := Index.ofGraph g
  let mut edges : Array Edge := Array.mkEmpty g.edges.size
  for n in g.nodes do
    if !drawn n.name then continue
    -- Walk backwards from `n` through the nodes not drawn, remembering whether
    -- the path so far has stayed inside statements.
    let mut best : Std.HashMap Name EdgeKind := {}
    let mut stack : Array (Name × EdgeKind) :=
      (idx.neighbours true n.name).map fun d => (d, idx.edgeKind.getD (d, n.name) .proof)
    while !stack.isEmpty do
      let (u, k) := stack.back!
      stack := stack.pop
      -- Revisit a node only when arriving on a strictly better path, so that a
      -- dependency reachable both through a statement and through a proof is
      -- recorded as the statement dependency it also is.
      match best[u]? with
      | some .statement => continue
      | some .proof => if k != .statement then continue
      | none => pure ()
      best := best.insert u k
      if drawn u then continue
      for d in idx.neighbours true u do
        let step := idx.edgeKind.getD (d, u) .proof
        let k' := if k == .statement && step == .statement then EdgeKind.statement else .proof
        stack := stack.push (d, k')
    for (u, k) in best.toArray do
      if drawn u && u != n.name then
        edges := edges.push { src := u, tgt := n.name, kind := k }
  return { g with
    nodes := g.nodes.filter (drawn ·.name)
    edges := edges.qsort fun a b =>
      if a.src == b.src then Name.lt a.tgt b.tgt else Name.lt a.src b.src }

/-! ## JSON -/

/-- A node, as serialized. Names are strings so that the format stays readable
and independent of Lean's `Name` encoding. -/
structure NodeJson where
  /-- Full declaration name. -/
  name : String
  /-- Declaring module. -/
  module : String
  /-- `Kind.toString`. -/
  kind : String
  /-- `Rank.toString`. -/
  rank : String
  /-- Whether the declaration is private. -/
  isPrivate : Bool
  /-- Whether the declaration is unsafe or partial. -/
  isUnsafe : Bool
  /-- Whether the declaration itself contains `sorry`. -/
  hasSorry : Bool
  /-- Whether it transitively depends on `sorry`. -/
  sorryTainted : Bool
  /-- Custom axioms used directly. -/
  customAxioms : Array String
  /-- Whether it transitively depends on a custom axiom. -/
  axiomTainted : Bool
  deriving ToJson, FromJson

/-- An edge, as serialized. -/
structure EdgeJson where
  /-- The dependency. -/
  src : String
  /-- The dependent. -/
  tgt : String
  /-- `EdgeKind.toString`. -/
  kind : String
  deriving ToJson, FromJson

/-- A whole graph, as serialized. -/
structure GraphJson where
  /-- The module prefixes the graph was extracted for. -/
  roots : Array String
  /-- The declarations. -/
  nodes : Array NodeJson
  /-- The dependencies. -/
  edges : Array EdgeJson
  deriving ToJson, FromJson

/-- Parse a dotted string as a `Name`. Only used on names this tool itself
emitted, so no escaping subtleties arise. -/
def nameOfString (s : String) : Name :=
  s.splitOn "." |>.foldl (init := Name.anonymous) fun acc part =>
    if part.isEmpty then acc else Name.str acc part

/-- Serialize a graph. -/
def Graph.toJson (g : Graph) : Json :=
  let nodes := g.nodes.map fun n =>
    { name := n.name.toString
      module := n.module.toString
      kind := n.kind.toString
      rank := n.rank.toString
      isPrivate := n.isPrivate
      isUnsafe := n.isUnsafe
      hasSorry := n.hasSorry
      sorryTainted := n.sorryTainted
      customAxioms := n.customAxioms.map (·.toString)
      axiomTainted := n.axiomTainted : NodeJson }
  let edges := g.edges.map fun e =>
    { src := e.src.toString, tgt := e.tgt.toString, kind := e.kind.toString : EdgeJson }
  Lean.toJson { roots := g.roots.map (·.toString), nodes, edges : GraphJson }

/-- Deserialize a graph, so that slicing and rendering can be re-run without
paying for the import of the project (and its Mathlib) again. -/
def Graph.fromJson? (j : Json) : Except String Graph := do
  let g : GraphJson ← Lean.fromJson? j
  let nodes ← g.nodes.mapM fun n => do
    let some kind := Kind.ofString? n.kind | throw s!"unknown kind: {n.kind}"
    let some rank := Rank.ofString? n.rank | throw s!"unknown rank: {n.rank}"
    return { name := nameOfString n.name
             module := nameOfString n.module
             kind, rank
             isPrivate := n.isPrivate
             isUnsafe := n.isUnsafe
             hasSorry := n.hasSorry
             sorryTainted := n.sorryTainted
             customAxioms := n.customAxioms.map nameOfString
             axiomTainted := n.axiomTainted : Node }
  let edges ← g.edges.mapM fun e => do
    let some kind := EdgeKind.ofString? e.kind | throw s!"unknown edge kind: {e.kind}"
    return { src := nameOfString e.src, tgt := nameOfString e.tgt, kind : Edge }
  return { roots := g.roots.map nameOfString, nodes, edges }

end ResultGraph
