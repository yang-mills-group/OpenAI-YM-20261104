import YM.Integration.WilsonIndependentConditionedBankOptics
import YM.Integration.WilsonAddressedTrialKineticAperture

/-! Both aperture prices on the selected original slow course and its measured kinetic scale. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankBerth
open Filter Lattice RG Wilson PhysicalNext.Repeat.Legato
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
open WilsonInvariantActionPosition (berth)
open scoped Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
local notation "a" => R.family.S.a

include simple slow in
theorem acquired (t:ℕ):∀ᶠ f:ℕ in atTop,
    let g:=thermal R f; let K:=berth R t f
    f<K ∧ 0<g ∧ g≤1 ∧ g^(2*(t+1))≤a K/a f ∧ a K/a f≤g^(2*t):=by
  filter_upwards [WilsonAddressedCollarWindow.original R simple slow t zero_lt_one] with f window
  let B:=R.family.path.levels.clock.hatBeta f
  let K:=berth R t f
  have b1:1≤B:=(R.family.path.levels.fits.delayed f).le
  have bp:0<B:=zero_lt_one.trans_le b1
  have g1:thermal R f≤1:=inv_le_one_of_one_le₀ (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt b1)
  have top:a f/a K≤B^(t+1):=by simpa only [Real.rpow_one,pow_succ] using window.2.2
  have reverse: (B^(t+1))⁻¹≤a K/a f:=by
    rw [←inv_div (a f) (a K)]
    exact (inv_le_inv₀ (pow_pos bp _) (div_pos (R.family.S.a_pos _) (R.family.S.a_pos _))).2 top
  refine ⟨window.1,inv_pos.mpr (Real.sqrt_pos.mpr bp),g1,?_,WilsonAddressedTrialKineticAperture.scale R t f⟩
  have sq:thermal R f^2=B⁻¹:=by
    change ((Real.sqrt B)⁻¹)^2=B⁻¹
    rw [inv_pow,Real.sq_sqrt bp.le]
  rw [pow_mul,sq,inv_pow]
  exact reverse

include simple slow in
theorem order (t q H:ℕ)(P D ζ:ℝ)(gain:0≤ζ)
    (low:P+D≤((2*t:ℕ):ℝ)*ζ)(high:P+D≤((q+1:ℕ):ℝ)-((2*(t+1):ℕ):ℝ)*H):
    ∀ᶠ f:ℕ in atTop,let g:=thermal R f;let K:=berth R t f;let δ:=a K/a f
      f<K ∧ g^(-D)*(δ^ζ+|g|^(q+1)*(δ^H)⁻¹)≤2*g^P:=by
  filter_upwards [acquired R simple slow t] with f band
  refine ⟨band.1,?_⟩
  apply WilsonIndependentConditionedBankOptics.order _ _ ((2*t:ℕ):ℝ) ((2*(t+1):ℕ):ℝ) ζ D P q H
    band.2.1 band.2.2.1 gain _ _ low high
  · simpa only [Real.rpow_natCast] using band.2.2.2.2
  · simpa only [Real.rpow_natCast] using band.2.2.2.1

end YM.Integration.WilsonIndependentConditionedBankBerth
