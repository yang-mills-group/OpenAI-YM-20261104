import YM.FormalBulk08.Annex.Palm
import YM.Integration.WilsonPointChildTestCoordinates
import YM.Integration.WilsonPointChildTestJet

/-! A genuine smooth test in the sup-norm half-cell and its physical
    Euclidean representative have equal pointed jets in the same axes. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildAddress
open YM Lattice RG Laurent FormalBulk08 Dawn Pose Next.Foundations PhysicalNext.Repeat.Legato
open WilsonCoeffUV.Embroider WilsonPointChildTestSupport WilsonNeutralPointCourse WilsonPointChildTestJet
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{d D:ℕ}


open WilsonPointChildTestCoordinates
theorem original (R:Run G)(digit:∀j,Site (R.family.S.block j))(t j:ℕ):
    (WilsonPointChildTestSupport.points R digit t j).val∈Annex.beam:=by
  induction t generalizing j with
  | zero=>apply Annex.cube_test.mpr;intro i;norm_num [WilsonPointChildTestSupport.points,origin]
  | succ n ih=>
    let a:Annex.Deck:=⟨_,ih (j+1)⟩
    exact Annex.peninsula_in _ (R.family.S.block_odd j) (Elm.growL R.family.path.levels j) (digit j) a

def seat (R:Run G)(digit:∀j,Site (R.family.S.block j))(t j:ℕ):Chamber:=
  ⟨coordinates (WilsonPointChildTestSupport.points R digit t j).val,by
    change ‖coordinates (WilsonPointChildTestSupport.points R digit t j).val - 0‖ ≤ (2:ℝ)⁻¹
    rw [sub_zero]
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    simpa [WilsonPointChildTestCoordinates.coordinates,Real.norm_eq_abs,one_div] using (Annex.cube_test.mp (original R digit t j) i)⟩

theorem common (R:Run G)(digit:∀j,Site (R.family.S.block j))(t j:ℕ)(p:Scroll D)(k:Brush D):
    (physical p).val k (WilsonPointChildTestSupport.points R digit t j)=(page D p).val k (seat R digit t j):=by
  let y:=(WilsonPointChildTestSupport.points R digit t j).val
  change iteratedFDeriv ℝ (k.1:ℕ) (p.val ∘ coordinates) y (basis ∘ k.2)=
    iteratedFDeriv ℝ (k.1:ℕ) p.val (coordinates y) (dot ∘ k.2)
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right coordinates (scribble p le_rfl) _
    (Nat.cast_le.mpr (Nat.le_of_lt_succ k.1.isLt)),ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp [Function.comp_def,WilsonPointChildTestCoordinates.axis]

end YM.Integration.WilsonPointChildAddress
