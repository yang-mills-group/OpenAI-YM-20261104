import YM.Integration.NativePaidPacketColors

/-! A fixed clearing order for the original selected packet read.
Only occupied rows require a strict lower bound. Positive powers may grow
without changing this clearing order. The original analytic vacuum is retained. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace YM.Integration.NativePaidPacketColorsAt

open Function Filter Set Metric Finset Lattice Wilson RG Marker Precision Multi Exterior
open LocalComparison
open Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology BigOperators ContDiff Classical

variable {V : Type} [DecidableEq V] {R : Census V}
variable {D : V → ComparisonDensity.Address.Orbit} {G : Gauge} {n : Side}
variable {P : MarkedPackets D G n R}

def exponent (B : ℕ) (z : ℤ) : ℕ := ((B : ℤ) + z).toNat

private lemma exponent_positive (B : ℕ) (z : ℤ) (hz : 0 < (B : ℤ) + z) :
    0 < exponent B z := by
  unfold exponent
  omega

private lemma exponent_eq (B : ℕ) (z : ℤ) (hz : 0 < (B : ℤ) + z) :
    (exponent B z : ℤ) = (B : ℤ) + z := by
  unfold exponent
  omega

private lemma total_grade (B : ℕ) (z : ℤ) (hz : 0 < (B : ℤ) + z) :
    B ≤ exponent B z + (-z).toNat := by
  have he := exponent_eq B z hz
  omega

private lemma fiber_positive (B : ℕ)
    (hfloor : ∀ i T, P.packet i = some T → 0 < (B : ℤ) + P.power i)
    (s : R.Mode) (z : ℤ) (i : NativePaidPacketGroups.Fiber P s z) :
    0 < (B : ℤ) + z := by
  simpa only [i.property.2.1] using
    hfloor i.val (NativePaidPacketGroups.token P s z i)
      (NativePaidPacketGroups.token_eq P s z i)

private lemma value_zero (B : ℕ)
    (hfloor : ∀ i T, P.packet i = some T → 0 < (B : ℤ) + P.power i)
    (s : R.Mode) (z : ℤ) (hz : ¬ 0 < (B : ℤ) + z)
    (x : TestSpace D) (U : Config G n) :
    NativePaidPacketSeries.value P s z x U = 0 := by
  unfold NativePaidPacketSeries.value
  calc
    _ = ∑' _i : NativePaidPacketGroups.Fiber P s z, (0 : ℂ) :=
      tsum_congr fun i => False.elim (hz (fiber_positive B hfloor s z i))
    _ = 0 := tsum_zero

private lemma clear_scalar (B : ℕ) (z : ℤ) (hz : 0 < (B : ℤ) + z)
    (g : ℝ) (a : ℂ) :
    (g ^ B) • ((g : ℂ) ^ z * a) = (g ^ exponent B z) • a := by
  by_cases hg : g = 0
  · subst g
    have he : exponent B z ≠ 0 := ne_of_gt (exponent_positive B z hz)
    by_cases hB : B = 0
    · subst B
      have hz0 : z ≠ 0 := by omega
      rw [Complex.ofReal_zero, (zero_zpow z hz0 : (0 : ℂ) ^ z = 0)]
      simp [he]
    · simp [hB, he]
  have hgC : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg
  have hc : (g : ℂ) ^ B * (g : ℂ) ^ z = (g : ℂ) ^ exponent B z := by
    calc
      _ = (g : ℂ) ^ ((B : ℤ) + z) := by
        simpa only [zpow_natCast] using (zpow_add₀ hgC (B : ℤ) z).symm
      _ = _ := by rw [← exponent_eq B z hz, zpow_natCast]
  simpa only [Complex.real_smul, Complex.ofReal_pow, mul_assoc] using
    congrArg (fun b : ℂ => b * a) hc

variable [Fintype V]

/-- The chosen clearing order changes neither the original packet read nor vacuum. -/
def colorsAt (P : MarkedPackets D G n R) (B : ℕ)
    (vacuum : ℝ → Config G n → ℝ) (x : TestSpace D) : Bulk.Colors R G n where
  vac := vacuum
  mark s g U := (g ^ B) • (P.read x g U).part s.val
  power _ := B

theorem colorsAt_default (P : MarkedPackets D G n R)
    (vacuum : ℝ → Config G n → ℝ) (x : TestSpace D) :
    colorsAt P (NativePaidPacketColors.commonPower P) vacuum x =
      NativePaidPacketColors.colors P vacuum x := rfl

variable {p : BudgetPoint} {address : V → Support n}
variable {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
variable {w : V → ℝ} {g0 width budget : ℝ} {offset slope : ℕ}
variable (paid : P.Paid p address region w g0 width budget offset slope)

include paid in
/-- Every original power fibre remains in the all-coupling polynomial identity. -/
theorem mark_polynomial (B : ℕ)
    (hfloor : ∀ i T, P.packet i = some T → 0 < (B : ℤ) + P.power i)
    (hg0 : g0 ≠ 0) (vacuum : ℝ → Config G n → ℝ)
    (x : TestSpace D) (s : Hot R) (g : ℝ) (U : Config G n) :
    (colorsAt P B vacuum x).mark s g U =
      ∑ z ∈ NativePaidPacketColors.powers P,
        (g ^ exponent B z) • NativePaidPacketSeries.value P s.val z x U := by
  change (g ^ B) • (P.read x g U).part s.val = _
  rw [NativePaidPacketColors.read_mode_sum paid hg0 s.val
    ((Cumulants.hot_iff_ne _).1 s.property), smul_sum]
  apply sum_congr rfl
  intro z _
  by_cases hz : 0 < (B : ℤ) + z
  · exact clear_scalar B z hz g _
  · rw [value_zero B hfloor s.val z hz x U]
    simp only [mul_zero, smul_zero]

include paid in
/-- The literal projected identity, including coupling zero, used by contact. -/
theorem projected_polynomial (B : ℕ)
    (hfloor : ∀ i T, P.packet i = some T → 0 < (B : ℤ) + P.power i)
    (hg0 : g0 ≠ 0) (vacuum : ℝ → Config G n → ℝ)
    (x : TestSpace D) (s : Hot R) :
    Bulk.projected ((colorsAt P B vacuum x).mark s) =
      (fun y : ℝ × fieldDir G n 1 =>
        ∑ z ∈ NativePaidPacketColors.powers P,
          (y.1 ^ exponent B z) •
            NativePaidPacketSeries.value P s.val z x (represent y.2)) :=
  funext fun y => mark_polynomial paid B hfloor hg0 vacuum x s y.1 (represent y.2)

include paid in
theorem colorsAt_well (B : ℕ)
    (hfloor : ∀ i T, P.packet i = some T → 0 < (B : ℤ) + P.power i)
    (hg0 : g0 ≠ 0) (vacuum : ℝ → Config G n → ℝ)
    (hv : GradeAt 3 (Bulk.projected vacuum))
    (hG : ∀ g, GaugeInvariant (vacuum g))
    (hE : ∀ g, Envelope (vacuum g)) (x : TestSpace D) :
    Bulk.Well (colorsAt P B vacuum x) := by
  refine ⟨hv, ?_, hG, ?_, hE, ?_⟩
  · intro s
    change GradeAt B (Bulk.projected ((colorsAt P B vacuum x).mark s))
    rw [projected_polynomial paid B hfloor hg0 vacuum x s]
    apply GradeAt.list_sum
    intro z _
    by_cases hz : 0 < (B : ℤ) + z
    · have hp := GradeAt.shifts (fun y : ℝ × fieldDir G n 1 => y.1)
        contDiffAt_fst rfl (exponent B z)
      have hq := (NativePaidPacketSeries.value_grade paid hg0 s.val
        ((Cumulants.hot_iff_ne _).1 s.property) z x).coarse
        (g := fun y : ℝ × fieldDir G n 1 => y.2) contDiffAt_snd rfl
      exact (hp.scale hq).lower (total_grade B z hz)
    · have he :
          (fun y : ℝ × fieldDir G n 1 =>
            (y.1 ^ exponent B z) •
              NativePaidPacketSeries.value P s.val z x (represent y.2)) =
          (fun _ => (0 : ℂ)) := by
        funext y
        rw [value_zero B hfloor s.val z hz x (represent y.2), smul_zero]
      rw [he]
      exact GradeAt.grade_zero B
  · intro s g t U
    simp_rw [mark_polynomial paid B hfloor hg0 vacuum x s]
    apply sum_congr rfl
    intro z _
    rw [NativePaidPacketSeries.value_gauge paid s.val z x t U]
  · intro s g
    have hs := (Cumulants.hot_iff_ne _).1 s.property
    have henv z := NativePaidPacketSeries.value_envelope paid hg0 s.val hs z x
    choose M hM using fun z => (henv z).cost
    have he : (colorsAt P B vacuum x).mark s g =
        (fun U => ∑ z ∈ NativePaidPacketColors.powers P,
          (g ^ exponent B z) • NativePaidPacketSeries.value P s.val z x U) :=
      funext (mark_polynomial paid B hfloor hg0 vacuum x s g)
    rw [he]
    refine ⟨Finset.measurable_sum _ (fun z _ =>
      (measurable_const : Measurable (fun _ : Config G n =>
        (g ^ exponent B z : ℝ))).smul (henv z).meas),
      ∑ z ∈ NativePaidPacketColors.powers P,
        ‖g ^ exponent B z‖ * M z, fun U => ?_⟩
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro z _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hM z U) (norm_nonneg _)

include paid in
theorem colorsAt_markedLog (B : ℕ) (hg0 : g0 ≠ 0)
    (vacuum : ℝ → Config G n → ℝ) (x : TestSpace D)
    (g : ℝ) (hg : g ≠ 0) (U : Config G n) :
    Integral.markedLog g U (colorsAt P B vacuum x) = P.read x g U := by
  ext s
  by_cases hs : s = R.quiet
  · subst s
    have hq : (P.read x g U).part R.quiet = 0 := by
      have he := congrArg (fun Q : Poly R => Q.part R.quiet)
        (NativePaidPacketColors.colors_markedLog paid hg0 vacuum x g hg U)
      simpa only [Integral.markedLog, part_lit_quiet] using he.symm
    rw [Integral.markedLog, part_lit_quiet, hq]
  · let t : Hot R := ⟨s, (Cumulants.hot_iff_ne _).2 hs⟩
    rw [Integral.markedLog, show ∀ f : Hot R → ℂ, (lit R f).part s = f t
      from fun f => part_lit f t]
    change (g ^ B)⁻¹ • ((g ^ B) • (P.read x g U).part s) = _
    exact inv_smul_smul₀ (pow_ne_zero _ hg) _

include paid in
theorem input_colorsAt (B : ℕ)
    (hfloor : ∀ i T, P.packet i = some T → 0 < (B : ℤ) + P.power i)
    (hg0 : g0 ≠ 0) (vacuum : ℝ → Config G n → ℝ)
    (hv : GradeAt 3 (Bulk.projected vacuum))
    (hG : ∀ g, GaugeInvariant (vacuum g))
    (hE : ∀ g, Envelope (vacuum g)) :
    InputColors (colorsAt P B vacuum) P where
  well := colorsAt_well paid B hfloor hg0 vacuum hv hG hE
  vacuum _ _ := rfl
  power _ _ := rfl
  marks := colorsAt_markedLog paid B hg0 vacuum

end YM.Integration.NativePaidPacketColorsAt
end
