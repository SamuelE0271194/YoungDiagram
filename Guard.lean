import YoungDiagram.Theorem6
import DeclAudit

open DeclAudit Lean Meta

section Repo

-- Total number of sorried declarations in the repo
#eval (dumpDeclAxioms "YoungDiagram").run'

end Repo

section Axiom

/--
info: 'Pi.isMutation_iff_transGen_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Pi.isMutation_iff_transGen_step

/--
info: Pi.isMutation_iff_transGen_step {X Y : ↥Variety.Pi} : IsMutation ↑X ↑Y ↔ Relation.TransGen Pi.Step X Y
-/
#guard_msgs in
#check Pi.isMutation_iff_transGen_step

/--
info: 'MixPiLambda.isMutation_iff_transGen_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MixPiLambda.isMutation_iff_transGen_step

/--
info: MixPiLambda.isMutation_iff_transGen_step {X Y : ↥(Variety.Mix (Variety.Pi, Variety.Lambda))} :
  IsMutation ↑X ↑Y ↔ Relation.TransGen MixPiLambda.Step X Y
-/
#guard_msgs in
#check MixPiLambda.isMutation_iff_transGen_step

/--
info: 'MixLambdaPi.isMutation_iff_transGen_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MixLambdaPi.isMutation_iff_transGen_step

/--
info: MixLambdaPi.isMutation_iff_transGen_step {X Y : ↥(Variety.Mix (Variety.Lambda, Variety.Pi))} :
  IsMutation ↑X ↑Y ↔ Relation.TransGen MixLambdaPi.Step X Y
-/
#guard_msgs in
#check MixLambdaPi.isMutation_iff_transGen_step

/--
info: 'Mix2LambdaPi.isMutation_iff_transGen_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Mix2LambdaPi.isMutation_iff_transGen_step

/--
info: Mix2LambdaPi.isMutation_iff_transGen_step {X Y : ↥(Variety.Mix (2 • Variety.Lambda, Variety.Pi))} :
  IsMutation ↑X ↑Y ↔ Relation.TransGen Mix2LambdaPi.Step X Y
-/
#guard_msgs in
#check Mix2LambdaPi.isMutation_iff_transGen_step

/--
info: 'MixPi2Lambda.isMutation_iff_transGen_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MixPi2Lambda.isMutation_iff_transGen_step

/--
info: MixPi2Lambda.isMutation_iff_transGen_step {X Y : ↥(Variety.Mix (Variety.Pi, 2 • Variety.Lambda))} :
  IsMutation ↑X ↑Y ↔ Relation.TransGen MixPi2Lambda.Step X Y
-/
#guard_msgs in
#check MixPi2Lambda.isMutation_iff_transGen_step

end Axiom

section Anchor

/--
info: SPEC_HASH target=Pi.isMutation_iff_transGen_step checked=53 hash=10855589601801731613
-/
#guard_msgs in
#eval (DeclAudit.dumpSpecClosureHash "YoungDiagram"
  `Pi.isMutation_iff_transGen_step).run'

/--
info: SPEC_HASH target=MixPiLambda.isMutation_iff_transGen_step checked=71 hash=4571517657258858861
-/
#guard_msgs in
#eval (DeclAudit.dumpSpecClosureHash "YoungDiagram"
  `MixPiLambda.isMutation_iff_transGen_step).run'

/--
info: SPEC_HASH target=MixLambdaPi.isMutation_iff_transGen_step checked=71 hash=17472563842929608527
-/
#guard_msgs in
#eval (DeclAudit.dumpSpecClosureHash "YoungDiagram"
  `MixLambdaPi.isMutation_iff_transGen_step).run'

/--
info: SPEC_HASH target=MixPi2Lambda.isMutation_iff_transGen_step checked=91 hash=3649446175573455644
-/
#guard_msgs in
#eval (DeclAudit.dumpSpecClosureHash "YoungDiagram"
  `MixPi2Lambda.isMutation_iff_transGen_step).run'

/--
info: SPEC_HASH target=Mix2LambdaPi.isMutation_iff_transGen_step checked=91 hash=1035756251374054183
-/
#guard_msgs in
#eval (DeclAudit.dumpSpecClosureHash "YoungDiagram"
  `Mix2LambdaPi.isMutation_iff_transGen_step).run'

end Anchor
