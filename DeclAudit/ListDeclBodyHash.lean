import YoungDiagram
import DeclAudit.Common

open Lean Meta

namespace DeclAudit

def hashString {α : Sort u} [Hashable α] (a : α) : String :=
  toString (hash a)

def bodyHashString (info : ConstantInfo) : String :=
  match info with
  | .defnInfo v => hashString v.value
  | .thmInfo _ => "<proof-skipped>"
  | .opaqueInfo v => hashString v.value
  | .axiomInfo _ => "<axiom>"
  | .inductInfo v => s!"<ctors:{formatNames v.ctors.toArray}>"
  | .ctorInfo _ => "<ctor>"
  | .recInfo _ => "<recursor>"
  | .quotInfo _ => "<quot>"

def projectConstantsInExpr
    (projectDecls : Std.HashSet Name)
    (self : Name)
    (expr : Expr) : Array Name := Id.run do
  let mut deps := #[]
  for usedName in expr.getUsedConstants do
    if usedName != self && projectDecls.contains usedName then
      deps := pushName deps usedName
  return deps

def collectProjectSpecDeps
    (projectDecls : Std.HashSet Name)
    (name : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut deps := #[]
  let collectExpr (start : Array Name) (e : Expr) : Array Name :=
    mergeNames start (projectConstantsInExpr projectDecls name e)
  match env.checked.get.find? name with
  | some (.axiomInfo v) =>
      deps := collectExpr deps v.type
  | some (.defnInfo v) =>
      deps := collectExpr deps v.type
      deps := collectExpr deps v.value
  | some (.thmInfo v) =>
      -- Proof terms are intentionally not part of the specification snapshot.
      deps := collectExpr deps v.type
  | some (.opaqueInfo v) =>
      deps := collectExpr deps v.type
      deps := collectExpr deps v.value
  | some (.quotInfo _) =>
      pure ()
  | some (.ctorInfo v) =>
      deps := collectExpr deps v.type
  | some (.recInfo v) =>
      deps := collectExpr deps v.type
  | some (.inductInfo v) =>
      deps := collectExpr deps v.type
      for ctor in v.ctors do
        if ctor != name && projectDecls.contains ctor then
          deps := pushName deps ctor
  | none =>
      pure ()
  return deps.qsort Name.lt

structure SpecClosureCache where
  memo : Std.HashMap Name (Array Name) := {}
  visiting : NameSet := {}

abbrev SpecClosureM := ReaderT (Std.HashSet Name) (StateT SpecClosureCache MetaM)

partial def collectSpecClosureFromDecl (name : Name) : SpecClosureM (Array Name) := do
  if let some deps := (← get).memo[name]? then
    return deps
  if (← get).visiting.contains name then
    return #[]
  modify fun st => { st with visiting := st.visiting.insert name }
  let projectDecls ← read
  let directDeps ← liftM <| collectProjectSpecDeps projectDecls name
  let mut closure := #[]
  for dep in directDeps do
    closure := pushName closure dep
    let transitiveDeps ← collectSpecClosureFromDecl dep
    closure := mergeNames closure transitiveDeps
  let sortedClosure := closure.qsort Name.lt
  modify fun st =>
    { memo := st.memo.insert name sortedClosure
      visiting := st.visiting.erase name }
  return sortedClosure

def targetTypeProjectDeps
    (projectDecls : Std.HashSet Name)
    (target : Name) : MetaM (Array Name) := do
  match (← getCheckedConst? target) with
  | some info =>
      return (projectConstantsInExpr projectDecls target info.type).qsort Name.lt
  | none =>
      throwError "unknown declaration {target}"

def collectSpecClosureForTarget
    (modulePrefix : String)
    (target : Name) : MetaM (Array Name) := do
  let projectDecls ← projectDeclSet modulePrefix
  ensureProjectDecl modulePrefix projectDecls target
  let directDeps ← targetTypeProjectDeps projectDecls target
  let mut closure := directDeps
  for dep in directDeps do
    let transitiveDeps ← (collectSpecClosureFromDecl dep).run projectDecls |>.run {}
    closure := mergeNames closure transitiveDeps.1
  return closure.qsort Name.lt

def depsField (deps : Array Name) : String :=
  String.intercalate "," (deps.map Name.toString).toList

def printDeclHashTsv (projectDecls : Std.HashSet Name) (name : Name) : MetaM Unit := do
  match (← getCheckedConst? name) with
  | some info =>
      let deps ← collectProjectSpecDeps projectDecls name
      let kind := kindOf info
      let typeHash := hashString info.type
      let bodyHash := bodyHashString info
      let deps := depsField deps
      IO.println
        s!"DECL\t{name}\t{kind}\t{typeHash}\t{bodyHash}\t{deps}"
  | none =>
      IO.println s!"MISSING\t{name}"

def dumpSpecClosureBodyHashes
    (modulePrefix : String)
    (target : Name) : MetaM Unit := do
  let projectDecls ← projectDeclSet modulePrefix
  ensureProjectDecl modulePrefix projectDecls target
  match (← getCheckedConst? target) with
  | some targetInfo =>
      let directDeps ← targetTypeProjectDeps projectDecls target
      let closure ← collectSpecClosureForTarget modulePrefix target
      let kind := kindOf targetInfo
      let typeHash := hashString targetInfo.type
      let deps := depsField directDeps
      IO.println s!"TARGET\t{target}\t{kind}\t{typeHash}\t{deps}"
      for name in closure do
        printDeclHashTsv projectDecls name
      IO.println s!"SUMMARY target={target} checked={closure.size}"
  | none =>
      throwError "unknown declaration {target}"

end DeclAudit

-- 目标 theorem 的 statement/type 所引用的项目内定义闭包：
#eval! (DeclAudit.dumpSpecClosureBodyHashes "YoungDiagram" `exists_mutation_le).run'
