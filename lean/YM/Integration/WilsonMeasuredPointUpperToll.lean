import YM.Integration.WilsonMeasuredPointApertureWage

/-! The small coupling on every late original slice, with the
purchase before the upper cutoff or period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPointUpperToll
open Filter Wilson RG Lattice PhysicalNext.Repeat.Legato
open scoped Topology
variable {G:Gauge} (R:Run G)
theorem small (simple:G.Simple) (a:ℝ):
    ∀ᶠ i:ℕ in atTop,∀ N per:ℕ,i≤N → ∀p:ℕ,0<p →
    a*(ConnectedActivityE6.Coat.gStep (R.family.path.rep N per i).beta)^p≤1:=by
  let t:=max 1 a
  have one:1≤t:=le_max_left _ _
  have tp:0<t:=zero_lt_one.trans_le one
  have hats:=RG01.Physical.hats simple R.alloy.B.a
  filter_upwards [hats.eventually_ge_atTop (2*t^2)] with i thick N per cut p pp
  let β:=(R.family.path.rep N per i).beta
  let g:=(Real.sqrt β)⁻¹
  have band:(R.alloy.B.a.clock.hatBeta i)/2≤β:=(R.makes.wilson.represents N per i cut).band.1
  have bs:t^2≤β:=by linarith only [thick,band]
  have sr:t≤Real.sqrt β:=by simpa only [Real.sqrt_sq tp.le] using Real.sqrt_le_sqrt bs
  have inv:g≤t⁻¹:=inv_anti₀ tp sr
  have gp:0≤g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have g1:g≤1:=inv.trans (inv_le_one_of_one_le₀ one)
  have less:g^p≤g:=by simpa only [pow_one] using pow_le_pow_of_le_one gp g1 (show 1≤p by omega)
  change a*g^p≤1
  calc
    a*g^p ≤ t*t⁻¹:=mul_le_mul (le_max_right _ _) (less.trans inv) (pow_nonneg gp _) tp.le
    _ = 1:=mul_inv_cancel₀ tp.ne'

end YM.Integration.WilsonMeasuredPointUpperToll
end
