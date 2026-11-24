import YM.Integration.WilsonGaussianSourcePolynomial
import YM.Integration.ManuscriptQLocalScalarDirectionalGerm

/-! Price the completely expanded coefficients of the *measured* Gaussian scalar
on the original and on the genuinely changed tree with the same coarse tests. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonGaussianSourceProfiles
open Marker Bloch FullQLocal.RenderedStep Function Filter Matrix Lattice Wilson RG RG.Shoot Tree Precision Exterior
open Pressure Supply Pressure.Testing Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open PhysicalAffineScalarIdealSquare
open PhysicalAffineScalarAperture (noHole)
open AnalyticBridge.SectorAffine.Offset (Through)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

private theorem test {X : Type} {ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (v : ι→X) (l : List ι) {n : ℕ} (hl : l.length ≤ n)
    {a b e : X→ℝ} (decomposition : ∀ y, a y=b y+e y)
    {m C : ℝ} (smooth : ContDiffAt ℝ l.length b 0) (value : jet v b l 0=m)
    (paid : Through n e 0 C) :
    |jet v a l 0-m| ≤ C*∏ i : Fin l.length,‖v (l.get i)‖ := by
  have h : a=fun y => b y+e y := funext decomposition
  rw [h,jet_add v l smooth (smooth_of_le paid.smooth hl),value,add_sub_cancel_left]
  have proj := (iteratedFDeriv ℝ l.length e 0).le_opNorm (v ∘ l.get)
  exact proj.trans (mul_le_mul_of_nonneg_right (paid.pay _ hl) (Finset.prod_nonneg fun i _ => norm_nonneg _))

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "c₀" => R.family.side d.level d.period
local notation "E" => (FreeResolvent.Slot G c₀ 1 → ℝ)
local notation "hole" => noHole S
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "g₀" => coupling (R.family.path.rep d.cutoff d.period (d.level+1)).beta

/-- Arbitrary signed and repeated external tests at any paid jet order. The constants
here are taken from the existing native allowance for the measured cutoff defect. -/
theorem tested {ι : Type*} {order : ℕ→ℕ→ℕ} (p : ManuscriptQLocalIdealSquare.Paid order R.kit)
    (k : (S).Choices) (q : Chi) (a : ℝ) (z : Site c₀) (U : {U : Forest (S).ratio // changed S d.forest U z})
    (Y : LinkArray G (Frozen hole θ d.forest)) (Z : LinkArray G (Frozen hole θ U.val)) (o : Site c₀)
    {n : ℕ} {C K : ℝ} (hd : n ≤ order j₁ j₀)
    (ordinary : Through n (ManuscriptQLocalScalarDirections.error R d k d.forest q a Y o) 0 C)
    (tagged : Through n (fun B => ManuscriptQLocalScalarDirections.error R d k U.val q a Z o B-
      ManuscriptQLocalScalarDirections.error R d k d.forest q a Y o B) 0 K)
    (v : ι→E) (l : List ι) (hl : l.length ≤ n) :
    |jet v (ManuscriptQLocalStoredGaussianScalar.stored R d k d.forest q a Y o) l 0-
      WilsonGaussianSourcePolynomial.polynomial R d k d.forest o v l g₀| ≤ C*∏ i : Fin l.length,‖v (l.get i)‖ ∧
    |jet v (fun B => ManuscriptQLocalStoredGaussianScalar.stored R d k U.val q a Z o B-
        ManuscriptQLocalStoredGaussianScalar.stored R d k d.forest q a Y o B) l 0-
      (WilsonGaussianSourcePolynomial.polynomial R d k U.val o v l g₀-
        WilsonGaussianSourcePolynomial.polynomial R d k d.forest o v l g₀)| ≤ K*∏ i : Fin l.length,‖v (l.get i)‖ := by
  obtain ⟨hf,eF⟩ := WilsonGaussianSourcePolynomial.physical R d p k d.forest o v l (hl.trans hd)
  obtain ⟨hu,_⟩ := WilsonGaussianSourcePolynomial.physical R d p k U.val o v l (hl.trans hd)
  have diff := WilsonGaussianSourcePolynomial.changed R d p k d.forest z U o v l (hl.trans hd)
  constructor
  · apply test v l hl _ hf eF ordinary
    intro B
    unfold ManuscriptQLocalScalarDirections.error
    abel
  · apply test v l hl _ (hu.sub hf) diff tagged
    intro B
    unfold ManuscriptQLocalScalarDirections.error
    abel

end YM.Integration.WilsonGaussianSourceProfiles
