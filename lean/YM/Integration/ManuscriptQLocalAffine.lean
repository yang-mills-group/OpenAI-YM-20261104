import YM.Integration.ActualKernelIdentification
import YM.Integration.RunFormalChain
import YM.Integration.FullQLocalNumericStepData
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Charges
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.CutGerm

/-! Compare the actual uncut Gaussian used by the formal generator with the
physical all-live Gram inverse. The finite walk cutoff has its original
two-sided exponentially weighted error all the way to the represented Hessian. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalAffine
open Function Matrix Lattice Wilson RG Precision Marker Exterior Tree
open PhysicalNext.Repeat.Legato Comparison.RG02 Pressure Pressure.Stores Pressure.Testing
open Next SectorChange Rows Gaussian Schur Wisps FreeResolvent
open AnalyticBridge.GaussianFieldAlignment AnalyticBridge.LocalGaussianLaws
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [DecidableEq I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "nativeBed" => R.alloy.B.M.H d.cutoff (d.level+1)
local notation "Y" => RunFormalChain.fromRun R
local notation "K" => d.kernel Y

/-- Identity of the uncut flat Gram and the actual physical Hessian, for
every original forest/physical tag selected in the requested local datum. -/
theorem precision (k : (Δ).Choices) :
    hessian d.forest k (T).high (T).up 0 0 =
      Affine.primary Δ d.forest k (T).high (T).up Affine.all 0 := by
  have hpath := CommonConstruction.runAlong_actual_path R d.cutoff (d.level+1) d.period d.below
  have home := (CommonConstruction.runAlong R).home d.forest d.below
  have hp : Bid.Prismatic d.forest (T).high (T).up := by
    change Bid.Prismatic d.forest (R.family.path.levels.params (d.level+1)).clip
      (R.alloy.B.kin.path d.cutoff (d.level+1))
    rw [← hpath]
    exact fun u => (home.2.1.2.2 u).1
  have hc : Bid.Comptroller d.forest nativeBed (T).high (T).up := by
    change Bid.Comptroller d.forest nativeBed (R.family.path.levels.params (d.level+1)).clip
      (R.alloy.B.kin.path d.cutoff (d.level+1))
    rw [← hpath]
    exact home.2.2.1
  exact (FreeResolvent.Tests.checked_loop d.forest nativeBed k _ _ hp hc).trans
    (Affine.identifies Δ d.forest k (R.family.path.levels.blocks d.level d.period).branches
      (R.alloy.B.support.cap d.cutoff (d.level+1) d.below)
      (R.alloy.B.support.links d.cutoff (d.level+1) d.below)
      (R.alloy.B.plan.all d.cutoff (d.level+1) d.below _).roots
      (R.kit.pledging.conducts.full d.cutoff (d.level+1) _ d.below)).symm

theorem covariance (k : (Δ).Choices) :
    (Affine.primary Δ d.forest k (T).high (T).up Affine.all 0)⁻¹ =
      (K).covariance d.forest k := by
  rw [← precision R d k]
  exact (ActualKernelIdentification.covariance_path R Y d.cutoff d.period d.level d.below d.forest k).symm

local notation "emptyStores" => bareStores Δ
local notation "coordinateAt" θ:arg => In θ emptyStores d.forest (G:=G)
local notation "presentAt" θ:arg => live emptyStores d.forest θ (G:=G)
local notation "actualGram" θ:arg tag:arg =>
  Rows.gram T θ (1 : Config G (R.family.side d.level d.period)) tag (shots Δ θ) emptyStores d.forest
local notation "uncutGram" θ:arg tag:arg =>
  freePart emptyStores d.forest θ T tag Affine.all

/-- On the empty stores every native free key participates, so inversion
commutes with the original relabeling on the complete coordinate set. -/
theorem all_keys (θ : ℝ) (tag : (Δ).Choices) :
    (uncutGram θ tag)⁻¹ = ((K).covariance d.forest tag).submatrix (presentAt θ) (presentAt θ) := by
  let a := (Assembly.opened G Δ θ emptyStores d.forest (Assembly.bare_is_Clear Δ θ d.forest)).symm
  change ((Affine.primary Δ d.forest tag (T).high (T).up Affine.all 0).submatrix a a)⁻¹ = _
  rw [inverse_reindex,covariance R d tag]
  rfl

private theorem inverse_charge {α : Type} [Fintype α] [DecidableEq α] {n : Side}
    (A B : Matrix α α ℝ) (p : α → Site n) {s M ε : ℝ}
    (ha : A.PosDef) (hb : B.PosDef) (hs : 0 ≤ s)
    (a : Pours A⁻¹ p p s M) (b : Pours B⁻¹ p p s M) (gap : Pours (A - B) p p s ε) :
    Pours (A⁻¹ - B⁻¹) p p s (M * ε * M) := by
  have h : B⁻¹ - A⁻¹ = B⁻¹ * (A - B) * A⁻¹ := by
    have ha₀ : IsUnit (A + (0 : ℝ) • 1).det := by
      simpa only [zero_smul,add_zero,isUnit_iff_ne_zero] using ha.det_pos.ne'
    have hb₀ : IsUnit (B + (0 : ℝ) • 1).det := by
      simpa only [zero_smul,add_zero,isUnit_iff_ne_zero] using hb.det_pos.ne'
    simpa only [resolve,zero_smul,add_zero] using FreeResolvent.resolve_diff ha₀ hb₀
  have eqn : A⁻¹ - B⁻¹ = (-1 : ℝ) • (B⁻¹ * (A - B) * A⁻¹) := by
    rw [neg_one_smul,← h,neg_sub]
  rw [eqn]
  simpa using (((b.fuse gap hs).fuse a hs).scale (-1))

/-- The rooted price of the inverse walk cutoff, with the actual original
Hessian in the subtraction and genuine inverse prices at both ends. -/
theorem cut (θ : ℝ) (tag : (Δ).Choices) {s η M D : ℝ}
    (h : Ready emptyStores d.forest θ T tag (1 : Config G (R.family.side d.level d.period)) s η M D)
    (hs : 0 ≤ s) :
    Pours ((show Gaussian.Table (coordinateAt θ) from (actualGram θ tag)⁻¹) -
      (show Gaussian.Table (coordinateAt θ) from ((K).covariance d.forest tag).submatrix (presentAt θ) (presentAt θ)))
      (Wisps.front emptyStores d.forest) (Wisps.front emptyStores d.forest) s
        (M*(Real.exp (-s*till θ)*D)*M) := by
  rw [← all_keys R d θ tag]
  have f := h.free Affine.all
  exact inverse_charge (actualGram θ tag) (uncutGram θ tag) (Wisps.front emptyStores d.forest)
    h.ends.source_pos f.source_pos hs h.ends.exactInv f.exactInv (h.level rfl)

end YM.Integration.ManuscriptQLocalAffine
end
