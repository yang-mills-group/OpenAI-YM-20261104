import YM.Integration.WilsonMatrixOriginalCurvatureField
import YM.Integration.WilsonReportingMeasuredWardClock

/-! The entire submitted grade-four centre and its curvature part are paid by
the literal quota on the original upper field, at the actual reporting date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermEntryTariff
open Finset Filter Lattice Wilson RG RG17 Spec Extraction Source
open PhysicalNext.Repeat.Legato Trace.Physical Maxwell StressFlux FVA2 MS.Local.Physical
open WilsonMatrixTicketLanesNativePrices WilsonMatrixTicketLanesReportedPivot
open WilsonMatrixOriginalIndependentColumns WilsonMatrixOriginalIndependentFields
open WilsonMatrixOriginalCurvatureStock WilsonMatrixOriginalIndependentLimit
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (B:Deck G)

theorem entries (k N p:ℕ) (v:R.family.label 4):
    ∑q,‖amounts R B k p (center R k N p v) q‖ ≤
      Next.UVStress.quota R.family 4 k N p v * fare (warehouse R) B 4:=by
  let x:=((R.family.factory 4 N p).entries k ((R.family.factory 4 N p).terminal.symm v)).x
  have h:(R.family.factory 4 k p).terminal.symm (center R k N p v)=x:=
    (R.family.factory 4 k p).terminal.symm_apply_apply x
  change (∑q,‖weights (warehouse R) B 4 ((R.family.factory 4 k p).terminal.symm (center R k N p v)) q‖)≤
    ((warehouse R).scene 4).coeffSize x * fare (warehouse R) B 4
  rw [h]
  exact bounded (warehouse R) B 4 x

private theorem thermometer {θ u b:ℝ} (hθ:0<θ) (hu:0<u) (upper:u≤2)
    (bill:((u*θ)^2)⁻¹≤2*b): (θ^2)⁻¹≤8*b:=by
  have one:(θ^2)⁻¹=u^2*((u*θ)^2)⁻¹:=by field_simp [hθ.ne',hu.ne']
  have u2:u^2≤(4:ℝ):=by nlinarith [mul_nonneg (sub_nonneg.mpr upper) (show 0≤2+u by linarith)]
  calc
    _=u^2*((u*θ)^2)⁻¹:=one
    _≤4*((u*θ)^2)⁻¹:=mul_le_mul_of_nonneg_right u2 (by positivity)
    _≤4*(2*b):=mul_le_mul_of_nonneg_left bill (by norm_num)
    _=_:=by ring

theorem funded {f:Extraction.Order} {S:Table R.family.book} {F:Final R.family f S}
    (L:Layout F) (U:Ultrafilter (ℕ×ℕ)) (cut:(U:Filter _)≤L.lens)
    (τ:ℕ→ℝ) (climate:Climate R U τ) (k N p:ℕ) (v:R.family.label 4) {M:ℝ}
    (deposit:(R.family.S.a k^4)⁻¹*Next.UVStress.quota R.family 4 k N p v≤M):
    let θ:=R.family.path.levels.clock.threshold k
    let a:=amounts R B k p (center R k N p v)
    (θ^2)⁻¹*(R.family.S.a k^4)⁻¹*(∑j,‖(stock B a).2 j‖) ≤
      8*R.family.path.levels.clock.hatBeta k * (M*fare (warehouse R) B 4):=by
  let a:=amounts R B k p (center R k N p v)
  let θ:=R.family.path.levels.clock.threshold k
  let s:=(R.family.S.a k^4)⁻¹
  let C:=fare (warehouse R) B 4
  have hs:0 ≤ s :=inv_nonneg.mpr (pow_pos (R.family.S.a_pos _) _).le
  have hC:0≤C:=sum_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _
  have bound:=WilsonReportingMeasuredWardClock.original L U cut τ climate k
  have hθ:0<θ:=(R.family.path.levels.budget k).threshold_pos
  have hot: (θ^2)⁻¹≤8*R.family.path.levels.clock.hatBeta k:=
    thermometer hθ (climate k).1 (climate k).2.1 bound.2.1
  have fee:s*(∑j,‖(stock B a).2 j‖)≤M*C:=by
    calc
      _ ≤ s*(Next.UVStress.quota R.family 4 k N p v*C):=mul_le_mul_of_nonneg_left ((bill B a).trans (entries R B k N p v)) hs
      _=(s*Next.UVStress.quota R.family 4 k N p v)*C:=by ring
      _≤M*C:=mul_le_mul_of_nonneg_right deposit hC
  change (θ^2)⁻¹*s*_≤_*(M*C)
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_right hot (mul_nonneg hs (sum_nonneg fun _ _=>norm_nonneg _))).trans
    (mul_le_mul_of_nonneg_left fee (le_trans (inv_nonneg.mpr (sq_nonneg θ)) hot))

end YM.Integration.WilsonMatrixOriginalGermEntryTariff
