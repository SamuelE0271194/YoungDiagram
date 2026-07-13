import YoungDiagram
import DeclAudit.Common

open Lean Meta

namespace DeclAudit

def collectProjectDirectDeps
    (projectDecls : Std.HashSet Name)
    (name : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut deps := #[]
  let collectExpr (start : Array Name) (e : Expr) : MetaM (Array Name) := do
    let mut acc := start
    for usedName in e.getUsedConstants do
      if usedName != name && projectDecls.contains usedName then
        acc := pushName acc usedName
    return acc
  match env.find? name with
  | some (.axiomInfo v) =>
      deps ← collectExpr deps v.type
  | some (.defnInfo v) =>
      deps ← collectExpr deps v.type
      deps ← collectExpr deps v.value
  | some (.thmInfo v) =>
      deps ← collectExpr deps v.type
      deps ← collectExpr deps v.value
  | some (.opaqueInfo v) =>
      deps ← collectExpr deps v.type
      deps ← collectExpr deps v.value
  | some (.quotInfo _) =>
      pure ()
  | some (.ctorInfo v) =>
      deps ← collectExpr deps v.type
  | some (.recInfo v) =>
      deps ← collectExpr deps v.type
  | some (.inductInfo v) =>
      deps ← collectExpr deps v.type
      for ctor in v.ctors do
        if ctor != name && projectDecls.contains ctor then
          deps := pushName deps ctor
  | none =>
      pure ()
  return deps.qsort Name.lt

structure DependencyCache where
  memo : Std.HashMap Name (Array Name) := {}
  visiting : NameSet := {}

abbrev DependencyM := ReaderT (Std.HashSet Name) (StateT DependencyCache MetaM)

partial def collectProjectTransitiveDeps
    (root : Name)
    (name : Name) : DependencyM (Array Name) := do
  if let some deps := (← get).memo[name]? then
    return deps
  if (← get).visiting.contains name then
    return #[]
  modify fun st => { st with visiting := st.visiting.insert name }
  let projectDecls ← read
  let directDeps ← liftM <| collectProjectDirectDeps projectDecls name
  let mut deps := #[]
  for dep in directDeps do
    if dep != root then
      deps := pushName deps dep
    let transitiveDeps ← collectProjectTransitiveDeps root dep
    for transitiveDep in transitiveDeps do
      if transitiveDep != root then
        deps := pushName deps transitiveDep
  let sortedDeps := deps.qsort Name.lt
  modify fun st =>
    { memo := st.memo.insert name sortedDeps
      visiting := st.visiting.erase name }
  return sortedDeps

def dumpDirectDeps (modulePrefix : String) (name : Name) : MetaM Unit := do
  let projectDecls ← projectDeclSet modulePrefix
  ensureProjectDecl modulePrefix projectDecls name
  let deps ← collectProjectDirectDeps projectDecls name
  IO.println s!"DIRECT {name} : {formatNames deps}"

def dumpTransitiveDeps (modulePrefix : String) (name : Name) : MetaM Unit := do
  let projectDecls ← projectDeclSet modulePrefix
  ensureProjectDecl modulePrefix projectDecls name
  let deps ← (collectProjectTransitiveDeps name name).run projectDecls |>.run {}
  IO.println s!"TRANSITIVE {name} : {formatNames deps.1}"

def dumpAllDirectDeps (modulePrefix : String) : MetaM Unit := do
  let projectDecls ← projectDeclSet modulePrefix
  for name in (← analysisDecls modulePrefix) do
    let deps ← collectProjectDirectDeps projectDecls name
    IO.println s!"DIRECT {name} : {formatNames deps}"

def dumpAllTransitiveDeps (modulePrefix : String) : MetaM Unit := do
  let projectDecls ← projectDeclSet modulePrefix
  for name in (← analysisDecls modulePrefix) do
    let deps ← (collectProjectTransitiveDeps name name).run projectDecls |>.run {}
    IO.println s!"TRANSITIVE {name} : {formatNames deps.1}"

def printGraphNodeTsv (name : Name) : MetaM Unit := do
  IO.println s!"NODE\t{name}\t{← nodeKind name}"

def printGraphEdgeTsv (src dst : Name) : MetaM Unit := do
  IO.println s!"EDGE\t{src}\t{dst}"

def dumpGraphNodesTsv (modulePrefix : String) : MetaM Unit := do
  for name in ← analysisDecls modulePrefix do
    printGraphNodeTsv name

def dumpDirectGraphTsv (modulePrefix : String) : MetaM Unit := do
  let projectDecls ← projectDeclSet modulePrefix
  for name in ← analysisDecls modulePrefix do
    printGraphNodeTsv name
  for name in ← analysisDecls modulePrefix do
    for dep in (← collectProjectDirectDeps projectDecls name) do
      printGraphEdgeTsv name dep

def dumpTransitiveGraphTsv (modulePrefix : String) : MetaM Unit := do
  let projectDecls ← projectDeclSet modulePrefix
  for name in ← analysisDecls modulePrefix do
    printGraphNodeTsv name
  for name in ← analysisDecls modulePrefix do
    let deps ← (collectProjectTransitiveDeps name name).run projectDecls |>.run {}
    for dep in deps.1 do
      printGraphEdgeTsv name dep

def dumpDirectEdgesTsv (modulePrefix : String) : MetaM Unit := do
  let projectDecls ← projectDeclSet modulePrefix
  for name in ← analysisDecls modulePrefix do
    for dep in (← collectProjectDirectDeps projectDecls name) do
      printGraphEdgeTsv name dep

def dumpTransitiveEdgesTsv (modulePrefix : String) : MetaM Unit := do
  let projectDecls ← projectDeclSet modulePrefix
  for name in ← analysisDecls modulePrefix do
    let deps ← (collectProjectTransitiveDeps name name).run projectDecls |>.run {}
    for dep in deps.1 do
      printGraphEdgeTsv name dep

def transitiveClosureNodesForDecl
    (modulePrefix : String)
    (name : Name) : MetaM (Array Name) := do
  let projectDecls ← projectDeclSet modulePrefix
  ensureProjectDecl modulePrefix projectDecls name
  let deps ← (collectProjectTransitiveDeps name name).run projectDecls |>.run {}
  return (pushName deps.1 name).qsort Name.lt

def dumpDirectGraphTsvForDecl (modulePrefix : String) (name : Name) : MetaM Unit := do
  let projectDecls ← projectDeclSet modulePrefix
  ensureProjectDecl modulePrefix projectDecls name
  printGraphNodeTsv name
  for dep in (← collectProjectDirectDeps projectDecls name) do
    printGraphNodeTsv dep
  for dep in (← collectProjectDirectDeps projectDecls name) do
    printGraphEdgeTsv name dep

def dumpTransitiveGraphTsvForDecl (modulePrefix : String) (name : Name) : MetaM Unit := do
  let projectDecls ← projectDeclSet modulePrefix
  ensureProjectDecl modulePrefix projectDecls name
  let deps ← (collectProjectTransitiveDeps name name).run projectDecls |>.run {}
  printGraphNodeTsv name
  for dep in deps.1 do
    printGraphNodeTsv dep
  for dep in deps.1 do
    printGraphEdgeTsv name dep

def dumpDirectEdgesTsvForDecl (modulePrefix : String) (name : Name) : MetaM Unit := do
  let projectDecls ← projectDeclSet modulePrefix
  ensureProjectDecl modulePrefix projectDecls name
  for dep in (← collectProjectDirectDeps projectDecls name) do
    printGraphEdgeTsv name dep

def dumpTransitiveEdgesTsvForDecl (modulePrefix : String) (name : Name) : MetaM Unit := do
  let projectDecls ← projectDeclSet modulePrefix
  ensureProjectDecl modulePrefix projectDecls name
  let deps ← (collectProjectTransitiveDeps name name).run projectDecls |>.run {}
  for dep in deps.1 do
    printGraphEdgeTsv name dep

def dumpTransitiveInducedGraphTsvForDecl (modulePrefix : String) (name : Name) : MetaM Unit := do
  let projectDecls ← projectDeclSet modulePrefix
  ensureProjectDecl modulePrefix projectDecls name
  let nodes ← transitiveClosureNodesForDecl modulePrefix name
  let nodeSet := nameSetOf nodes
  for node in nodes do
    printGraphNodeTsv node
  for src in nodes do
    for dst in (← collectProjectDirectDeps projectDecls src) do
      if nodeSet.contains dst then
        printGraphEdgeTsv src dst

def dumpTransitiveInducedEdgesTsvForDecl (modulePrefix : String) (name : Name) : MetaM Unit := do
  let projectDecls ← projectDeclSet modulePrefix
  ensureProjectDecl modulePrefix projectDecls name
  let nodes ← transitiveClosureNodesForDecl modulePrefix name
  let nodeSet := nameSetOf nodes
  for src in nodes do
    for dst in (← collectProjectDirectDeps projectDecls src) do
      if nodeSet.contains dst then
        printGraphEdgeTsv src dst

end DeclAudit

-- 单个 declaration 的 direct 依赖：
#eval (DeclAudit.dumpDirectDeps "YoungDiagram" `Pi.X1_eq).run'

-- 单个 declaration 的 transitive 依赖闭包：
-- #eval (DeclAudit.dumpTransitiveDeps "YoungDiagram" `Pi.X1_eq).run'

-- 打印本项目全部 declaration 的 direct 依赖：
-- #eval (DeclAudit.dumpAllDirectDeps "YoungDiagram").run'

-- 打印本项目全部 declaration 的 transitive 依赖：
-- #eval (DeclAudit.dumpAllTransitiveDeps "YoungDiagram").run'
