import Lean

open Lean Meta

namespace DeclAudit

def kindOf : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "recursor"

def formatNames (names : Array Name) : String :=
  "[" ++ String.intercalate ", " (names.map Name.toString).toList ++ "]"

def oneLine (s : String) : String :=
  s.replace "\n" " "

def pushName (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name

def mergeNames (xs ys : Array Name) : Array Name :=
  ys.foldl pushName xs

def nameSetOf (names : Array Name) : Std.HashSet Name :=
  names.foldl (fun acc name => acc.insert name) Std.HashSet.emptyWithCapacity

def analysisDecls (modulePrefix : String) : MetaM (Array Name) := do
  let env ← getEnv
  let mut decls := #[]
  for i in [:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[i]!
    if moduleName.toString.startsWith modulePrefix then
      let moduleData := env.header.moduleData[i]!
      for j in [:moduleData.constNames.size] do
        decls := decls.push moduleData.constNames[j]!
  return decls

def projectDeclSet (modulePrefix : String) : MetaM (Std.HashSet Name) := do
  let decls ← analysisDecls modulePrefix
  return nameSetOf decls

def declSummary (name : Name) : MetaM String := do
  let env ← getEnv
  match env.checked.get.find? name with
  | some info =>
      let typeFmt ← ppExpr info.type
      let typeStr := oneLine typeFmt.pretty
      return s!"{name} : type={typeStr}"
  | none =>
      return s!"{name} : type=<unknown>"

def nodeKind (name : Name) : MetaM String := do
  let env ← getEnv
  match env.find? name with
  | some info => return kindOf info
  | none => return "unknown"

def ensureProjectDecl
    (modulePrefix : String)
    (projectDecls : Std.HashSet Name)
    (name : Name) : MetaM Unit := do
  if !projectDecls.contains name then
    throwError "{name} is not a declaration from modules matching prefix {modulePrefix}"

def getCheckedConst? (name : Name) : MetaM (Option ConstantInfo) := do
  return (← getEnv).checked.get.find? name

end DeclAudit
