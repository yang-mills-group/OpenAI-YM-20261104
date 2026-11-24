import YM.Integration.WilsonMovingForkPositionIntegrals

/-! Integrate the physical product and the reflected pairs on the common
exterior field against the same finite fitted independent coordinates. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSameEpochIntegrals
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
open WilsonMovingForkPositionIntegrals (nearTags twoTags)
open private jointCost oneCost from YM.Integration.WilsonMovingForkPositionIntegrals
open private finite from YM.Integration.WilsonMovingForkKernelIntegrals
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (J:ℝ→PhysMS.tower S){n:ℕ}(d:Fin n → ℕ)(h:ℕ)(Z:WilsonPrescription G)
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)
    {simple:G.Simple}{σ:Prescription (Press.portDeck G)}{branch:Bool}(ms:Main.Match Z simple M σ branch)
local notation "C" => R.family

variable {I:Type}[Fintype I]

include ν ms in
theorem whole_row (q:ℕ)(g s r t:ℝ)(tp:0<t)(ψ:Test n)(φ:Test 2)
    (safe:∀x∈tsupport ψ,∀z∈tsupport φ,placed r t x (relative z)∈conf (n+1))
    (fit:∀p∈space ψ φ,forest p.1 (squeeze (-s) (relative p.2))∈conf (n+1))
    (v:∀i,Free (C) (d i))(a:Free (C) h)(basis:I → Free (C) h)(coeff:I → ℂ){E:ℝ}
    (wage:∀p∈space ψ φ,‖S.useAt S (placed r t p.1 (relative p.2)) (nearTags F J d h Z (r:=r) (t:=t) v a)-
      ∑i,coeff i*fullAt (C) d h Z q g s v (basis i) p‖≤E):
    ‖appeared F (d:=d) (fun i=>homogeneous F J Z r (d i) (v i)) (stencil J φ tp ⟨h,active F J Z t h a⟩) r ψ-
      ∑i,coeff i*full (C) d h Z q g s v (basis i) ψ φ‖≤Read.Value ψ*Read.Value φ*E:=by
  let V:=fun i=>active F J Z r (d i) (v i)
  have eq:(fun i=>homogeneous F J Z r (d i) (v i))=fun i=>J r (d i) (V i):=by
    funext i;simp only [V,active,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
  let rows:=fun i=>fullAt (C) d h Z q g s v (basis i)
  have regular(i:I):ContinuousOn (rows i) (space ψ φ):=by
    obtain ⟨paid,_⟩:=WilsonMovingForkCanonicalKernels.regular (h:=h) Z M ν ms q g s ψ φ fit
    exact continuousOn_finsetSum _ (fun j _=>continuousOn_const.mul
      (continuousOn_finsetSum _ fun u _=>continuousOn_const.mul (paid _ _)))
  rw [eq,WilsonMovingForkPhysicalProducts.whole F J ψ φ tp V (active F J Z t h a) safe]
  simp_rw [(WilsonMovingForkKernelIntegrals.original (C) d h Z M ν ms q g s ψ φ fit).1]
  have joined:=finite (fun p:Points n×Points 2=>ψ p.1*φ p.2) rows coeff (fun i=>whole ψ φ (regular i))
  change (∑i,coeff i*tested ψ φ (rows i))=tested ψ φ (fun p=>∑i,coeff i*rows i p) at joined
  rw [joined]
  apply jointCost ψ φ _ _ _ _ wage
  · intro p hp
    exact (kernel F _ p (safe p.1 hp.1 p.2 hp.2)).continuousWithinAt
  · exact continuousOn_finsetSum _ fun i _=>continuousOn_const.mul (regular i)

include ν ms in
theorem gram_row (q:ℕ)(g s r t:ℝ)(tp:0<t)(ψ:Test n)(φ:Test 2)
    (fit:∀p∈space ψ φ,forest p.1 (squeeze (-s) (relative p.2))∈conf (n+1))
    (a:Free (C) h)(basis:I → Free (C) h)(coeff:I → ℂ)(k:Dframe.Toon G h){E:ℝ}
    (wage:∀z∈tsupport φ,‖S.useAt S (t • z) (twoTags F J h Z r t a k)-
      ∑i,coeff i*gramAt (C) h Z q g s (basis i) k z‖≤E):
    ‖φ.applyTo (fun z=>S.useAt S (t • z) (twoTags F J h Z r t a k))-
      ∑i,coeff i*gram (C) h Z q g s (basis i) φ k‖≤Read.Value φ*E:=by
  let rows:=fun i=>gramAt (C) h Z q g s (basis i) k
  have regular(i:I):ContinuousOn (rows i) (tsupport φ):=by
    obtain ⟨_,paid⟩:=WilsonMovingForkCanonicalKernels.regular (h:=h) Z M ν ms q g s ψ φ fit
    exact continuousOn_finsetSum _ (fun u _=>continuousOn_const.mul (paid _ _))
  simp_rw [(WilsonMovingForkKernelIntegrals.original (C) (fun _:Fin n=>0) h Z M ν ms q g s ψ φ fit).2]
  have joined:=finite φ rows coeff (fun i=>local_test φ _ (regular i))
  change (∑i,coeff i*φ.applyTo (rows i))=φ.applyTo (fun z=>∑i,coeff i*rows i z) at joined
  rw [joined]
  apply oneCost _ _ _ _ _ wage
  · apply (S.class_smooth S F.room.kernel.smooth _).continuousOn.comp (continuous_const_smul _).continuousOn
    exact fun z hz=>Work.A05.smul_conf tp (φ.tsupport_subset hz)
  · exact continuousOn_finsetSum _ fun i _=>continuousOn_const.mul (regular i)

end YM.Integration.WilsonMovingForkSameEpochIntegrals
end
