import YM.WilsonCoeffUV.Product.I.Cruise
import YM.WilsonCoeffUV.Product.Report.Center
import YM.Next.RANK.Coordinates

/-! Translation by a whole stop cell on the independent continued ordinary
word. This action uses the inherited top-N kinetic programme on every step. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialStoppedTranslation
open Finset Function Lattice RG Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer
open Precision Gauge Wilson WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open scoped Classical BigOperators
variable {G : Gauge} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
variable (A : Levels G) {O : ChartRatio G} (simple : G.Simple) (localCost : LocalRatio O)
variable {c w N k : ℕ} (top : c ≤ N) (X : Era G V) (auth : Auth k X)

include simple localCost top auth in
theorem original (live : w ≤ c) : ∀ z : Cover,
    cruises A O N k c w (shifted X ((A.S.toDepth live 0).count.val • z))=
      shifted (cruises A O N k c w X) z := by
  induction live using Nat.decreasingInduction with
  | self =>
    intro z
    rw [cruises_top,cruises_top]
    change shifted X ((A.S.steps c (c-c)).val • z)=_
    simp [Schedule.steps]
  | of_succ i hi ih =>
    intro z
    let H := A.S.toDepth (Nat.succ_le_of_lt hi) 0
    have fac : (A.S.toDepth hi.le 0).count.val=H.count.val*(A.S.block i).val :=
      Next.Rank.Station.size_comp (A.S.oneStep i 0) H (A.S.toDepth hi.le 0)
    rw [cruises_sub _ _ _ _ _ hi,cruises_sub _ _ _ _ X hi,fac,mul_smul]
    rw [ih]
    exact outing A (hi.trans_le top) simple localCost
      (cruising A simple localCost (Nat.succ_le_of_lt hi) top auth) z

include simple localCost top auth in
theorem emitted (live : w ≤ c) (z : Cover) (e : ℕ) :
    (cruises A O N k c w (shifted X ((A.S.toDepth live 0).count.val • z))).2 e 0 Fin.elim0=
      (cruises A O N k c w X).2 e 0 Fin.elim0 := by
  rw [original A simple localCost top X auth live]
  apply congrArg ((cruises A O N k c w X).2 e 0)
  exact Subsingleton.elim _ _

include simple localCost top in
theorem all_faces {I : Type*} [DecidableEq I] (mass : Finset I → ℕ)
    (face : Finset I → Era G V) (paid : ∀ s, Auth (mass s) (face s))
    (live : w ≤ c) (z : Cover) (s : Finset I) (e : ℕ) :
    (cruises A O N (mass s) c w
      (shifted (face s) ((A.S.toDepth live 0).count.val • z))).2 e 0 Fin.elim0=
      (cruises A O N (mass s) c w (face s)).2 e 0 Fin.elim0 :=
  emitted A simple localCost top (face s) (paid s) live z e

end YM.Integration.WilsonPositionProgramTrialStoppedTranslation
