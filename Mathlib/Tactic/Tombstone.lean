import Lean
import Mathlib.Util.Superscript

open Lean Parser.Term Mathlib

private def natOfNumLit : TSyntax ``num → Nat
  | ⟨.node _ _ c⟩ =>
    -- This is a little hacky
    match (c : Array Syntax)[0]? with
    | some a => TSyntax.getNat <| mkNode numLitKind #[a]
    | _ => 0
  | _ => 0

/-- Stores the result of the `getIthShadowedWithUserName` search. -/
private inductive GetIResult
  /-- `found fvarId` means that `fvarid` corresponds to the `i`-th local declaration with a given
  name. -/
  | found : FVarId → GetIResult
  /-- The constructor used when there is no local declaration with a given name. -/
  | noName
  /-- The constructor used when the index passed is larger than the number of local declarations
  with a given name. -/
  | idxError : Nat → GetIResult

/-- The core function used in the `tombstone%` elaborator. This retrieves the `idx`th shadowed
variable with (user)name `name`, counting backwards. -/
def Lean.LocalContext.getIthShadowedWithUserName (lctx : LocalContext) (name : Name) (idx : Nat) :
    GetIResult := Id.run do
  let n := lctx.numIndices
  let mut count := 0
  let mainDecl := lctx.findFromUserName? name
  for i in [:n] do
    -- Go through the declarations in reverse order
    match lctx.getAt? (n - i - 1) with
    | none => pure ()
    | some localDecl =>
      unless localDecl.userName.eraseMacroScopes == name do continue
      -- Test equality using the `FVarId`s since there's no `BEq` instance on `LocalDecls`
      -- in Lean core
      if some localDecl.fvarId == mainDecl.map LocalDecl.fvarId then continue
      if count == idx then return .found <| localDecl.fvarId
      count := count + 1
  if count == 0 then
    return .noName
  else
    return .idxError count

/-- `tombstone% name idx` retrieves the `idx`th *inaccessible* local declaration with (user)name
`name`. -/
elab "tombstone% " name:ident idx:num : term => do
  let lctx ← getLCtx
  let idxNat := natOfNumLit idx
  match lctx.getIthShadowedWithUserName name.getId idxNat with
  | .found fvarId => return .fvar fvarId
  | .noName =>
    throwErrorAt name s!"No declarations with name {name.getId} were found."
  | .idxError count =>
    throwErrorAt idx s!"The index {idxNat} is higher than the number of inaccessible variables
     with name {name.getId} (= {count})."


namespace Tombstone

/-- Shorthand for `superscript(num)`.

This is needed for the same reasons as `superscriptTerm`. -/
private def superscriptNum :=
  leading_parser (withAnonymousAntiquot := false) Mathlib.Tactic.superscript num

/-- `x✝ⁱ` retrives the `i-th` variable in the context with
identifier `x`, counting backwards (i.e. `✝x⁰` is simply calling
the variable `x`). This is useful when there are several variables with the same name.-/
scoped syntax:100 ident noWs "✝" optional(superscriptNum) : term

macro_rules
  | `(term|$x:ident✝$i:superscript) => `(tombstone% $x $(⟨i⟩))
  | `(term|$x:ident✝) => `(tombstone% $x 0)

example : 1 + 1 = 2 := by
  let x := 1
  let x := 2
  run_tac Lean.Elab.Tactic.withMainContext do
    let lctx ← getLCtx
    let idx := 0
    let name := `x
    let n := lctx.numIndices
    let mut count := 0
    let mainDecl := lctx.findFromUserName? name
    for i in [:n] do
      -- Go through the declarations in reverse order
      match lctx.getAt? (n - i - 1) with
      | none => pure ()
      | some localDecl =>
        Lean.logInfo m!"{(count : Nat)}"
        unless localDecl.userName.eraseMacroScopes == name do continue
        -- Test equality using the `FVarId`s since there's no `BEq` instance on `LocalDecls`
        -- in Lean core
        if some localDecl.fvarId == mainDecl.map LocalDecl.fvarId then continue
        if count == idx then return
        count := count + 1
  let a := x✝
  sorry

end Tombstone
