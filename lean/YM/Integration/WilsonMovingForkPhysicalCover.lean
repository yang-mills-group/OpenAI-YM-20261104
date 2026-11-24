import YM.Integration.WilsonMovingForkPrintedFile
import YM.Integration.WilsonPositionProgramTrialHomeCenters
import YM.Integration.WilsonPositionProgramTrialFixedDigits
import YM.Integration.WilsonMovingForkSeededPoint

/-! The same actual K sites and their genuine ancestors on the physical torus
and on the independently sampled cover. Period fitting precedes all upper cutoffs. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonMovingForkPhysicalCover
open Function Filter Finset Lattice RG Org Wilson Push AbsoluteSums
open WilsonCoeffUV.Bank
open PhysicalNext PhysicalNext.Repeat.Legato
open WilsonMovingForkPrintedFile (parent)
open WilsonMovingForkSeededPoint (seats)
open WilsonPositionProgramTrialCellDigits (packed)
open WilsonPositionProgramTrialFixedDigits (parents)
open scoped Classical Topology BigOperators
variable {G:Gauge}{n:ℕ}

theorem ancestor (R:Run G){i K:ℕ}(ik:i≤K)(per:ℕ)(o:Fin n → Cover):
    parent R ik per (fun a=>wrap (R.family.side K per) (o a))=
      fun a=>wrap (R.family.side i per) (parents R.family.S ik o a):=by
  let A:=R.family.S.toDepth ik per
  funext a
  have atChild:A.assemble (wrap (R.family.side i per) (parentC A.count (o a)),wrap A.count (o a))=
      wrap (R.family.side K per) (o a):=by
    rw [Ratio.assemble,A.embed_wrap,←map_add,packed]
  change A.parent (wrap (R.family.side K per) (o a))=wrap _ (parentC A.count (o a))
  exact (congrArg A.parent atChild.symm).trans (A.assemble_parent _)

theorem aligned (R:Run G){j K:ℕ}(cut:j≤K)(per:ℕ)(o:Fin n → Cover):
    (fun a=>wrap (R.family.side K per) (WilsonPositionProgramTrialHomeCenters.plant R.family.S cut o (fun _=>0) a))=
      seats (R:=R) cut per o:=by
  funext a
  have transfer:=(R.family.S.toDepth cut per).embed_wrap (o a)
  have count:(R.family.S.toDepth cut per).count=(R.family.S.toDepth cut 0).count:=rfl
  rw [count] at transfer
  simpa [WilsonPositionProgramTrialHomeCenters.plant,seats] using transfer.symm

theorem unwrapped (S:Schedule)(K:ℕ){I:Type}[Finite I](o:I → Cover):
    ∀ᶠ per:ℕ in atTop,∀i,lift (wrap (S.side K per) (o i))=o i:=by
  have grow:Tendsto (fun per=>(S.side K per).val) atTop atTop:=by
    refine tendsto_atTop_mono (f:=fun per=>(S.period per).val) ?_ S.period_strict.tendsto_atTop
    exact fun per=>le_mul_of_one_le_right (Nat.zero_le _) (S.denominator K).property
  refine eventually_all.mpr fun i=>?_
  have bound (a:Axis):∀ᶠ per:ℕ in atTop,
      -((S.side K per).val:ℤ)<2*o i a ∧ 2*o i a≤(S.side K per).val:=by
    filter_upwards [grow.eventually (eventually_gt_atTop (2*(o i a).natAbs))] with per large
    omega
  filter_upwards [eventually_all.mpr bound] with per fit using lift_eq_iff.mpr ⟨rfl,fit⟩

end YM.Integration.WilsonMovingForkPhysicalCover
