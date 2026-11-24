import YM.Integration.FVA1Physical.Round2.PhysicalVacuumRate

/-! Absorb the explicit regular-vacuum geometry cost into an arbitrary
coupling order slack uniformly over the whole physical beta band. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Filter Lattice RG Wilson Precision MSbar MSbar.Lis MSbar.Midpoint PhysicalNext.Repeat.Legato
open scoped Topology

theorem geometry_subpower (p q : ℕ) : Mosaic.Run atTop id (fun β => vacuumGeometry β p q) 0 := by
  have wide := Mosaic.Run.stanza (X:=(id : ℝ → ℝ)) tendsto_id
  have vol : Mosaic.Run atTop (id : ℝ → ℝ) Mosaic.vol 0 := by
    apply (wide.mulK tendsto_id (1/32)).alter
    filter_upwards with i
    change (1/32)*Mosaic.hatW i = Mosaic.hatW i/32
    ring
  have one := Mosaic.Run.token (X:=(id : ℝ → ℝ)) tendsto_id 1
  have a := vol.Ypow tendsto_id (q+1)
  have b := wide.Ypow tendsto_id (Alto.Dean (p+1))
  have c := (one.addR tendsto_id vol).Ypow tendsto_id (p+3)
  exact (Mosaic.Run.token tendsto_id (5*2^(p+1))).addR tendsto_id (a.Ymul tendsto_id (b.Ymul tendsto_id c))

theorem geometry_absorbed (p q : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ β : ℝ in atTop, ∀ γ : ℝ, β/2 ≤ γ →
      (Heath.Stock.cue γ)^(p+1) * vacuumGeometry β p q ≤
        (Heath.Stock.cue γ)^((p:ℝ)+1-η) := by
  filter_upwards [geometry_subpower p q (η/4) (by positivity),eventually_ge_atTop (4:ℝ)] with β hB hβ
  intro γ hγ
  have hp : 0 < β := by linarith
  have ht : 0 < γ := by linarith
  have hsq : β ≤ γ^2 := by nlinarith [mul_self_le_mul_self (show 0≤β/2 by positivity) hγ]
  have price : vacuumGeometry β p q ≤ γ^(η/2) := by
    apply (le_abs_self _).trans (hB.trans ?_)
    have h := Real.rpow_le_rpow hp.le hsq (show 0 ≤ η/4 by positivity)
    refine h.trans_eq ?_
    rw [← Real.rpow_natCast γ 2,← Real.rpow_mul ht.le]
    congr 1; push_cast; ring
  let g := Heath.Stock.cue γ
  have hg : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr ht)
  have hconvert : γ^(η/2) = g^(-η) := by
    change γ^(η/2) = ((Real.sqrt γ)⁻¹)^(-η)
    rw [Real.sqrt_eq_rpow,← Real.rpow_neg ht.le,← Real.rpow_mul ht.le]
    congr 1; ring
  rw [hconvert] at price
  calc
    _ ≤ g^(p+1)*g^(-η) := mul_le_mul_of_nonneg_left price (pow_nonneg hg.le _)
    _ = _ := by rw [← Real.rpow_natCast g (p+1),← Real.rpow_add hg]; congr 1; push_cast; ring

end YM.Integration.FVA1Physical.Round2
