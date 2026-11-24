import YM.Integration.WilsonMovingForkPhysicalProducts
import YM.Integration.WilsonMovingForkKernelIntegrals
import YM.Integration.WilsonPublicOutputSmooth

/-! Genuine position comparisons on the full joint and the two-point
ordinary row enter their separately positioned integrals with their true
profile masses. The output cap retains every lower source coefficient. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkPositionIntegrals
open Filter Function Set Finset MeasureTheory Lattice Wilson RG Source Extraction Table Spec RG17 Climb
open Trace.Pilot PhysMS PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open FVA2.O FVA2.O.Project FVA2.Scale FVA2.O.Score FVA2.O.Enh MS MS.Land MS.Fleet MS.Theater MS.Rake
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichTwoDatePivot
open WilsonMacroscopicRichSignedAmplitude WilsonMacroscopicRichPositionRows WilsonMacroscopicRichMovingPlane
open WilsonMSDictionaryVector WilsonPublicForkIndependentPlacement WilsonPublicForkIndependentFields
open WilsonPublicForkTestProduct WilsonMacroscopicRichTestGeometry WilsonMovingForkKernelIntegrals
open private whole from YM.Integration.WilsonPublicForkTestProduct
open private local_test from YM.Integration.WilsonMovingForkKernelIntegrals
open private kernel from YM.Integration.WilsonPublicForkInterchange
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (J:ℝ→PhysMS.tower S){n:ℕ}(d:Fin n → ℕ)(h:ℕ)(Z:WilsonPrescription G)
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)
    {simple:G.Simple}{σ:Prescription (Press.portDeck G)}{branch:Bool}(ms:Main.Match Z simple M σ branch)
local notation "C" => R.family

private theorem jointCost {n l:ℕ}(ψ:Test n)(φ:Test l)(u v:Points n×Points l → ℂ)
    (uc:ContinuousOn u (space ψ φ))(vc:ContinuousOn v (space ψ φ))
    {E:ℝ}(wage:∀p∈space ψ φ,‖u p-v p‖≤E):
    ‖tested ψ φ u-tested ψ φ v‖≤Read.Value ψ*Read.Value φ*E:=by
  unfold tested
  rw [←integral_sub (whole ψ φ uc) (whole ψ φ vc)]
  simp_rw [←mul_sub]
  exact mass ψ φ _ wage

private theorem oneCost (φ:Test 2)(u v:Points 2 → ℂ)(uc:ContinuousOn u (tsupport φ))(vc:ContinuousOn v (tsupport φ))
    {E:ℝ}(wage:∀z∈tsupport φ,‖u z-v z‖≤E):‖φ.applyTo u-φ.applyTo v‖≤Read.Value φ*E:=by
  unfold Test.applyTo
  rw [←integral_sub (local_test φ u uc) (local_test φ v vc)]
  simp_rw [←mul_sub]
  have paid:Integrable φ:=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  refine (norm_integral_le_of_norm_le (paid.norm.mul_const E) (Eventually.of_forall ?_)).trans_eq ?_
  · intro z
    by_cases hz:z∈tsupport φ
    · rw [norm_mul];exact mul_le_mul_of_nonneg_left (wage z hz) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hz]
  · rw [integral_mul_const]

def nearTags {r t:ℝ}(v:∀i,Free (C) (d i))(a:Free (C) h):Fin (n+1)→S.Tag:=
  WilsonMovingForkPhysicalProducts.roster J r t (fun i=>active F J Z r (d i) (v i)) (active F J Z t h a)

def twoTags (r t:ℝ)(a:Free (C) h)(k:Dframe.Toon G h):Fin 2→S.Tag:=
  Fin.cons ⟨h,homogeneous F J Z r h ((WilsonMSDictionaryVector.basis (C) h) k)⟩
    (fun _:Fin 1=>⟨h,homogeneous F J Z t h a⟩)

include ν ms in
theorem whole_row (q:ℕ)(g s r t:ℝ)(tp:0<t)(ψ:Test n)(φ:Test 2)
    (safe:∀x∈tsupport ψ,∀z∈tsupport φ,placed r t x (relative z)∈conf (n+1))
    (fit:∀p∈space ψ φ,forest p.1 (squeeze (-s) (relative p.2))∈conf (n+1))
    (v:∀i,Free (C) (d i))(a:Free (C) h){E:ℝ}
    (wage:∀p∈space ψ φ,‖S.useAt S (placed r t p.1 (relative p.2)) (nearTags F J d h Z (r:=r) (t:=t) v a)-
      fullAt (C) d h Z q g s v a p‖≤E):
    ‖appeared F (d:=d) (fun i=>homogeneous F J Z r (d i) (v i)) (stencil J φ tp ⟨h,active F J Z t h a⟩) r ψ-
      full (C) d h Z q g s v a ψ φ‖≤Read.Value ψ*Read.Value φ*E:=by
  let V:=fun i=>active F J Z r (d i) (v i)
  have eq:(fun i=>homogeneous F J Z r (d i) (v i))=fun i=>J r (d i) (V i):=by
    funext i;simp only [V,active,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
  rw [eq,WilsonMovingForkPhysicalProducts.whole F J ψ φ tp V (active F J Z t h a) safe,
    (WilsonMovingForkKernelIntegrals.original (C) d h Z M ν ms q g s ψ φ fit).1]
  apply jointCost ψ φ _ _ _ _ wage
  · intro p hp
    exact (kernel F _ p (safe p.1 hp.1 p.2 hp.2)).continuousWithinAt
  · obtain ⟨paid,_⟩:=WilsonMovingForkCanonicalKernels.regular (h:=h) Z M ν ms q g s ψ φ fit
    exact continuousOn_finsetSum _ (fun j _=>continuousOn_const.mul
      (continuousOn_finsetSum _ fun u _=>continuousOn_const.mul (paid _ _)))

include ν ms in
theorem gram_row (q:ℕ)(g s r t:ℝ)(tp:0<t)(ψ:Test n)(φ:Test 2)
    (fit:∀p∈space ψ φ,forest p.1 (squeeze (-s) (relative p.2))∈conf (n+1))
    (a:Free (C) h)(k:Dframe.Toon G h){E:ℝ}
    (wage:∀z∈tsupport φ,‖S.useAt S (t • z) (twoTags F J h Z r t a k)-gramAt (C) h Z q g s a k z‖≤E):
    ‖φ.applyTo (fun z=>S.useAt S (t • z) (twoTags F J h Z r t a k))-gram (C) h Z q g s a φ k‖≤Read.Value φ*E:=by
  rw [(WilsonMovingForkKernelIntegrals.original (C) (fun _:Fin n=>0) h Z M ν ms q g s ψ φ fit).2]
  apply oneCost _ _ _ _ _ wage
  · apply (S.class_smooth S F.room.kernel.smooth _).continuousOn.comp (continuous_const_smul _).continuousOn
    exact fun z hz=>Work.A05.smul_conf tp (φ.tsupport_subset hz)
  · obtain ⟨_,paid⟩:=WilsonMovingForkCanonicalKernels.regular (h:=h) Z M ν ms q g s ψ φ fit
    exact continuousOn_finsetSum _ (fun u _=>continuousOn_const.mul (paid _ _))

end YM.Integration.WilsonMovingForkPositionIntegrals
