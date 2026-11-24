import YM.Integration.WilsonLimitConstruction.FundedOriginalRun
import YM.Integration.WilsonMatrixTicketPhysicalMeshRows
import YM.RG17.Canvas
import YM.SharpGram.Load.Tents

/-! The original campaign's dense Gram coverage prices the actual moving
quotient frame on every supplied observing ultrafilter of the same final. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonMatrixTicketPhysicalLensRows

open Filter SharpGram Next.Rank PhysicalNext.Repeat.Legato
open scoped Topology
universe v

private theorem cancelTier (a M K q : ℝ) (ha : 0 < a) {j d : ℕ} (hj : j ≤ d) :
    (M * (K / a ^ d * q)) * a ^ (d-j) = (K * M / a ^ j) * q := by
  rw [show a ^ d = a ^ j * a ^ (d-j) by rw [← pow_add, Nat.add_sub_of_le hj]]
  field_simp [ha.ne']

/-- A single genuine Gram mantle prices both sides on this ultrafilter.
The primal lift retains its full moving labels.  The dual bound exposes the
operator norm of the fixed physical functional on the original measured frame. -/
theorem purchased {G : Gauge} (R : Run G) (simple : G.Simple) {ε : ℝ}
    {T : Campaign R} (W : Campaign.Pillars R T)
    (original : WilsonLimitConstruction.FundedOriginalProperties.{v} simple ε W)
    {f : Extraction.Order} {S : Table R.family.book} (physical : Spec.Final R.family f S)
    (service : OPE.Services R.family f S) (U : Ultrafilter (ℕ × ℕ))
    (hU : (U : Filter (ℕ × ℕ)) ≤ f.fuse) :
    ∃ B : Lenses.Mantle physical (U : Filter (ℕ × ℕ)), ∀ d : ℕ, ∀ᶠ m in atTop,
      (∀ x : S.Field d, ∃ (y : R.family.label d) (w : ℕ × ℕ → R.family.label d),
        S.project d y = x ∧ Tendsto w (U : Filter (ℕ × ℕ)) (𝓝 y) ∧
        ∀ᶠ i in (U : Filter (ℕ × ℕ)), Next.UVStress.quota R.family d m i.1 i.2 (w i) ≤
          2 * R.family.path.levels.clock.hatBeta m ^ Lenses.price d * R.family.S.a m ^ d *
            ‖(Load.tent B m d).symm x‖) ∧
      ∀ (j : ℕ), j ≤ d → ∀ (u : S.Field d →ₗ[ℂ] ℂ)
        (l : Filter (ℕ × ℕ)), l.NeBot → l ≤ (U : Filter (ℕ × ℕ)) →
        ∀ (w : ℕ × ℕ → R.family.label d) (z : R.family.label d) (q : ℝ),
          Tendsto w l (𝓝 z) →
          (∀ᶠ i in l, Next.UVStress.quota R.family d m i.1 i.2 (w i) ≤ q) →
          ‖u (S.project d z)‖ * R.family.S.a m ^ (d-j) ≤
            min ((‖LinearMap.toContinuousLinearMap (𝕜 := ℂ) (u.comp (S.project d))‖ *
                  Price.outward R.family d m * R.family.S.a m ^ (d-j)) * q)
                ((2 * Lenses.bonus R.family d *
                  ‖LinearMap.toContinuousLinearMap (𝕜 := ℂ) (u.comp (Load.tent B m d).toLinearMap)‖ /
                  R.family.S.a m ^ j) * q) := by
  obtain ⟨B⟩ := Lenses.attains_mantle17 physical service U hU original.2.1.coverage
  refine ⟨B, fun d => ?_⟩
  filter_upwards [Load.investors B service d, eventually_ge_atTop (R.family.ref d)] with m hm href
  refine ⟨hm.1, ?_⟩
  intro j hj u l hne hl w z q hw hq
  letI := hne
  refine le_min (WilsonMatrixTicketPhysicalMeshRows.moving physical href u (hl.trans hU) w z q hw hq) ?_
  let e := Load.tent B m d
  let row := LinearMap.toContinuousLinearMap (𝕜 := ℂ) (u.comp e.toLinearMap)
  have hx := hm.2 l hne hl w z q hq hw
  have hrow : ‖u (S.project d z)‖ ≤ ‖row‖ *
      (2 * Lenses.bonus R.family d / R.family.S.a m ^ d * q) := by
    calc
      _ = ‖row (e.symm (S.project d z))‖ := by
        change _ = ‖u (e (e.symm (S.project d z)))‖
        rw [LinearEquiv.apply_symm_apply]
      _ ≤ ‖row‖ * ‖e.symm (S.project d z)‖ := row.le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_left hx (norm_nonneg row)
  exact (mul_le_mul_of_nonneg_right hrow (pow_nonneg (R.family.S.a_pos m).le (d-j))).trans_eq <|
    cancelTier _ ‖row‖ (2 * Lenses.bonus R.family d) q (R.family.S.a_pos m) hj

/-- The full outward ticket forces a polynomial price for this same normalized
dual operator.  The test is the actual moving lift of each measured frame vector. -/
theorem necessary {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (physical : Spec.Final C f S) (service : OPE.Services C f S)
    (U : Ultrafilter (ℕ × ℕ)) (hU : (U : Filter (ℕ × ℕ)) ≤ f.fuse)
    (B : Lenses.Mantle physical (U : Filter (ℕ × ℕ)))
    (ticket : OPE.Outward C f S physical.sector.derivatives)
    {d j : ℕ} (hj : j ≤ d) (u : S.Field d →ₗ[ℂ] ℂ)
    (kill : ∀ c : ℕ, c < j → ∀ hc : c ≤ d, ∀ z : S.Field c,
      u (physical.sector.derivatives.rise hc z) = 0) :
    ∃ L : ℕ, ∀ᶠ m in atTop,
      ‖LinearMap.toContinuousLinearMap (𝕜 := ℂ) (u.comp (Load.tent B m d).toLinearMap)‖ /
        C.S.a m ^ j ≤ 2 * C.path.levels.clock.hatBeta m ^ (L + Lenses.price d) := by
  obtain ⟨L, hL⟩ := ticket.paper d j hj u kill
  refine ⟨L, ?_⟩
  filter_upwards [hL, Load.investors B service d] with m hm hI
  let e := Load.tent B m d
  let row := LinearMap.toContinuousLinearMap (𝕜 := ℂ) (u.comp e.toLinearMap)
  have hb : 0 ≤ C.path.levels.clock.hatBeta m := zero_le_one.trans (C.path.levels.fits.delayed m).le
  apply (div_le_iff₀ (pow_pos (C.S.a_pos m) j)).2
  apply row.opNorm_le_bound (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hb _))
    (pow_nonneg (C.S.a_pos m).le _))
  intro v
  obtain ⟨y, q, hy, hq, measured⟩ := hI.1 (e v)
  have measured' : ∀ᶠ i in (U : Filter (ℕ × ℕ)), Next.UVStress.quota C d m i.1 i.2 (q i) ≤
      2 * C.path.levels.clock.hatBeta m ^ Lenses.price d * C.S.a m ^ d * ‖v‖ := by
    simpa only [e, LinearEquiv.symm_apply_apply] using measured
  have price := hm (U : Filter (ℕ × ℕ)) inferInstance hU q y _ hq measured'
  rw [hy] at price
  apply le_of_mul_le_mul_right _ (pow_pos (C.S.a_pos m) (d-j))
  calc
    ‖row v‖ * C.S.a m ^ (d-j) ≤ C.path.levels.clock.hatBeta m ^ L *
        (2 * C.path.levels.clock.hatBeta m ^ Lenses.price d * C.S.a m ^ d * ‖v‖) := price
    _ = _ := by
      rw [pow_add, show C.S.a m ^ d = C.S.a m ^ j * C.S.a m ^ (d-j) by
        rw [← pow_add, Nat.add_sub_of_le hj]]
      ring

end YM.Integration.WilsonMatrixTicketPhysicalLensRows
end

