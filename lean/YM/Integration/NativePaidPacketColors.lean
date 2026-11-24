import YM.Integration.NativePaidPacketSeries
import YM.Integration.LocalComparisonInput

/-! Common-power Colors of the unchanged full selected packet sum.
All nonquiet modes and all original rows are retained. The definition uses
the original read at every coupling; finite power grouping is used only to
prove its analytic grade. The independent analytic vacuum is preserved. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace YM.Integration.NativePaidPacketColors

open Function Filter Set Metric Finset Lattice Wilson RG Marker Precision Multi Exterior
open LocalComparison NativePaidPacketGroups
open Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology BigOperators ContDiff Classical

variable {V : Type} [DecidableEq V] {R : Census V}
variable {D : V → ComparisonDensity.Address.Orbit} {G : Gauge} {n : Side}
variable (P : MarkedPackets D G n R)

def commonPower : ℕ := P.powerCap + 1
def powers : Finset ℤ := Icc (-(P.powerCap : ℤ)) (P.powerCap : ℤ)
def exponent (z : ℤ) : ℕ := (((commonPower P) : ℤ) + z).toNat

private def raw (x : TestSpace D) (U : Config G n) (i : ℕ) : ℂ :=
  match P.packet i with
  | none => 0
  | some T => T.read x U

private lemma token_raw (s : R.Mode) (z : ℤ) (x : TestSpace D)
    (U : Config G n) (i : (NativePaidPacketGroups.Fiber P) s z) :
    raw P x U i.val = ((NativePaidPacketGroups.token P) s z i).read x U := by
  rw [raw, (NativePaidPacketGroups.token_eq P) s z i]

private lemma indicator_eq (s : R.Mode) (z : ℤ) (x : TestSpace D)
    (U : Config G n) (i : ℕ) :
    Set.indicator {i | P.mode i = s ∧ P.power i = z ∧ (P.packet i).isSome}
      (raw P x U) i =
      if P.mode i = s ∧ P.power i = z then raw P x U i else 0 := by
  by_cases hm : P.mode i = s <;> by_cases hz : P.power i = z <;>
    cases hi : P.packet i <;> simp [Set.indicator, raw, hm, hz, hi]

private lemma group_eq (s : R.Mode) (z : ℤ) (x : TestSpace D) (U : Config G n) :
    NativePaidPacketSeries.value P s z x U =
      ∑' i, if P.mode i = s ∧ P.power i = z then raw P x U i else 0 := by
  calc
    _ = ∑' i : (NativePaidPacketGroups.Fiber P) s z, raw P x U i.val :=
      tsum_congr fun i => (token_raw P s z x U i).symm
    _ = _ := (_root_.tsum_subtype
      {i : ℕ | P.mode i = s ∧ P.power i = z ∧ (P.packet i).isSome}
      (raw P x U)).trans (tsum_congr (indicator_eq P s z x U))

variable {P} {p : BudgetPoint} {address : V → Support n}
variable {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
variable {w : V → ℝ} {g0 width budget : ℝ} {offset slope : ℕ}
variable (paid : P.Paid p address region w g0 width budget offset slope)

include paid in
private lemma group_summable (hg0 : g0 ≠ 0) (s : R.Mode) (hs : s ≠ R.quiet)
    (z : ℤ) (x : TestSpace D) (U : Config G n) :
    Summable (fun i => if P.mode i = s ∧ P.power i = z then raw P x U i else 0) := by
  have h := (NativePaidPacketSeries.value_summable paid hg0 s hs z x U).congr
    (fun i => (token_raw P s z x U i).symm)
  have hi := (summable_subtype_iff_indicator
    (s := {i : ℕ | P.mode i = s ∧ P.power i = z ∧ (P.packet i).isSome})
    (f := raw P x U)).mp h
  exact hi.congr (indicator_eq P s z x U)

private lemma active_power (i : ℕ)
    (T : Comparison.Density.RenderM.Token G n (fun v => (D v).Mood) (P.rank i))
    (hi : P.packet i = some T) : P.power i ∈ (powers P) := by
  have hb := P.power_bounded i T hi
  simp only [powers, Finset.mem_Icc]
  omega

include paid in
private lemma mode_sum (hg0 : g0 ≠ 0) (s : R.Mode) (hs : s ≠ R.quiet)
    (x : TestSpace D) (g : ℝ) (U : Config G n) :
    Summable (fun i => (Poly.send (P.mode i) (P.term x g U i)).part s) ∧
    (∑' i, (Poly.send (P.mode i) (P.term x g U i)).part s) =
      ∑ z ∈ (powers P), (g : ℂ) ^ z * NativePaidPacketSeries.value P s z x U := by
  let q (z : ℤ) (i : ℕ) :=
    (g : ℂ) ^ z * (if P.mode i = s ∧ P.power i = z then raw P x U i else 0)
  have hq z : Summable (q z) := (group_summable paid hg0 s hs z x U).mul_left _
  have he (i : ℕ) :
      (Poly.send (P.mode i) (P.term x g U i)).part s = ∑ z ∈ (powers P), q z i := by
    rw [Poly.part_send]
    cases hi : P.packet i with
    | none => simp [MarkedPackets.term, raw, q, hi]
    | some T =>
      have hp := active_power (P := P) i T hi
      by_cases hm : P.mode i = s
      · simp [MarkedPackets.term, raw, q, hi, hm, eq_comm, hp, mul_ite]
      · simp [q, hm, Ne.symm hm]
  refine ⟨(summable_sum (fun z _ => hq z)).congr (fun i => (he i).symm), ?_⟩
  rw [tsum_congr he, Summable.tsum_finsetSum (fun z _ => hq z)]
  apply sum_congr rfl
  intro z hz
  dsimp only [q]
  rw [tsum_mul_left, ← group_eq]

private lemma quiet_term (x : TestSpace D) (g : ℝ) (U : Config G n) (i : ℕ) :
    (Poly.send (P.mode i) (P.term x g U i)).part R.quiet = 0 := by
  cases hi : P.packet i with
  | none => simp [MarkedPackets.term, hi]
  | some T =>
    simp only [Poly.part_send, if_neg (Ne.symm (P.marked i T hi))]

variable [Fintype V]

include paid in
omit [Fintype V] in
theorem read_summable (hg0 : g0 ≠ 0) (x : TestSpace D) (g : ℝ) (U : Config G n) :
    Summable (fun i => Poly.send (P.mode i) (P.term x g U i)) := by
  apply Pi.summable.mpr
  intro s
  by_cases hs : s = R.quiet
  · subst s
    change Summable (fun i : ℕ => (Poly.send (P.mode i) (P.term x g U i)).part R.quiet)
    exact (summable_zero : Summable (fun _ : ℕ => (0 : ℂ))).congr
      (fun i => (quiet_term (P := P) x g U i).symm)
  · exact (mode_sum paid hg0 s hs x g U).1

include paid in
private lemma read_mode (hg0 : g0 ≠ 0) (s : R.Mode) (hs : s ≠ R.quiet)
    (x : TestSpace D) (g : ℝ) (U : Config G n) :
    (P.read x g U).part s =
      ∑ z ∈ (powers P), (g : ℂ) ^ z * NativePaidPacketSeries.value P s z x U := by
  unfold MarkedPackets.read
  rw [Poly.share (read_summable paid hg0 x g U)]
  exact (mode_sum paid hg0 s hs x g U).2

include paid in
private lemma read_quiet (hg0 : g0 ≠ 0) (x : TestSpace D) (g : ℝ) (U : Config G n) :
    (P.read x g U).part R.quiet = 0 := by
  unfold MarkedPackets.read
  rw [Poly.share (read_summable paid hg0 x g U)]
  simp only [quiet_term, tsum_zero]

variable (P)

/-- The raw mark is a single common power times the original full read. -/
def colors (vacuum : ℝ → Config G n → ℝ) (x : TestSpace D) : Bulk.Colors R G n where
  vac := vacuum
  mark s g U := (g ^ (commonPower P)) • (P.read x g U).part s.val
  power _ := (commonPower P)

variable {P}

omit [Fintype V] in
private lemma exponent_positive (z : ℤ) (hz : z ∈ (powers P)) :
    0 < (exponent P) z := by
  simp only [powers, Finset.mem_Icc] at hz
  unfold exponent commonPower
  omega

omit [Fintype V] in
private lemma exponent_eq (z : ℤ) (hz : z ∈ (powers P)) :
    ((exponent P) z : ℤ) = ((commonPower P) : ℤ) + z := by
  simp only [powers, Finset.mem_Icc] at hz
  unfold exponent commonPower
  omega

omit [Fintype V] in
private lemma total_grade (z : ℤ) (hz : z ∈ (powers P)) :
    (commonPower P) ≤ (exponent P) z + (-z).toNat := by
  have h := exponent_eq (P := P) z hz
  omega

omit [Fintype V] in
private lemma clear_scalar (z : ℤ) (hz : z ∈ (powers P)) (g : ℝ) (a : ℂ) :
    (g ^ (commonPower P)) • ((g : ℂ) ^ z * a) = (g ^ (exponent P) z) • a := by
  by_cases hg : g = 0
  · subst g
    simp [commonPower, ne_of_gt (exponent_positive z hz)]
  have hgC : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hg
  have hc : (g : ℂ) ^ (commonPower P) * (g : ℂ) ^ z = (g : ℂ) ^ (exponent P) z := by
    calc
      _ = (g : ℂ) ^ (((commonPower P) : ℤ) + z) := by
        simpa only [zpow_natCast] using
          (zpow_add₀ hgC ((commonPower P) : ℤ) z).symm
      _ = _ := by rw [← exponent_eq z hz, zpow_natCast]
  simpa only [Complex.real_smul, Complex.ofReal_pow, mul_assoc] using
    congrArg (fun b : ℂ => b * a) hc

include paid in
private lemma mark_polynomial (hg0 : g0 ≠ 0) (vacuum : ℝ → Config G n → ℝ)
    (x : TestSpace D) (s : Hot R) (g : ℝ) (U : Config G n) :
    (colors P vacuum x).mark s g U =
      ∑ z ∈ (powers P), (g ^ (exponent P) z) • NativePaidPacketSeries.value P s.val z x U := by
  change (g ^ (commonPower P)) • (P.read x g U).part s.val = _
  rw [read_mode paid hg0 s.val ((Cumulants.hot_iff_ne _).1 s.property), smul_sum]
  exact sum_congr rfl fun z hz => clear_scalar z hz g _

include paid in
theorem colors_well (hg0 : g0 ≠ 0) (vacuum : ℝ → Config G n → ℝ)
    (hv : GradeAt 3 (Bulk.projected vacuum))
    (hG : ∀ g, GaugeInvariant (vacuum g))
    (hE : ∀ g, Envelope (vacuum g)) (x : TestSpace D) :
    Bulk.Well (colors P vacuum x) := by
  refine ⟨hv, ?_, hG, ?_, hE, ?_⟩
  · intro s
    have he : Bulk.projected ((colors P vacuum x).mark s) =
        (fun y : ℝ × fieldDir G n 1 => ∑ z ∈ (powers P),
          (y.1 ^ (exponent P) z) • NativePaidPacketSeries.value P s.val z x (represent y.2)) :=
      funext fun y => mark_polynomial paid hg0 vacuum x s y.1 (represent y.2)
    rw [he]
    apply GradeAt.list_sum
    intro z hz
    have hp := GradeAt.shifts (fun y : ℝ × fieldDir G n 1 => y.1)
      contDiffAt_fst rfl ((exponent P) z)
    have hq := (NativePaidPacketSeries.value_grade paid hg0 s.val
      ((Cumulants.hot_iff_ne _).1 s.property) z x).coarse
      (g := fun y : ℝ × fieldDir G n 1 => y.2) contDiffAt_snd rfl
    exact (hp.scale hq).lower (total_grade z hz)
  · intro s g t U
    simp_rw [mark_polynomial paid hg0 vacuum x s]
    apply sum_congr rfl
    intro z hz
    rw [NativePaidPacketSeries.value_gauge paid s.val z x t U]
  · intro s g
    have hs := (Cumulants.hot_iff_ne _).1 s.property
    have henv z := NativePaidPacketSeries.value_envelope paid hg0 s.val hs z x
    choose M hM using fun z => (henv z).cost
    have he : (colors P vacuum x).mark s g =
        (fun U => ∑ z ∈ (powers P),
          (g ^ (exponent P) z) • NativePaidPacketSeries.value P s.val z x U) :=
      funext (mark_polynomial paid hg0 vacuum x s g)
    rw [he]
    refine ⟨Finset.measurable_sum _ (fun z _ =>
      (measurable_const : Measurable (fun _ : Config G n =>
        (g ^ (exponent P) z : ℝ))).smul (henv z).meas),
      ∑ z ∈ (powers P), ‖g ^ (exponent P) z‖ * M z, fun U => ?_⟩
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro z hz
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hM z U) (norm_nonneg _)

include paid in
theorem colors_markedLog (hg0 : g0 ≠ 0) (vacuum : ℝ → Config G n → ℝ)
    (x : TestSpace D) (g : ℝ) (hg : g ≠ 0) (U : Config G n) :
    Integral.markedLog g U (colors P vacuum x) = P.read x g U := by
  ext s
  by_cases hs : s = R.quiet
  · subst s
    rw [Integral.markedLog, part_lit_quiet, read_quiet paid hg0 x g U]
  · let t : Hot R := ⟨s, (Cumulants.hot_iff_ne _).2 hs⟩
    rw [Integral.markedLog, show ∀ f : Hot R → ℂ, (lit R f).part s = f t
      from fun f => part_lit f t]
    change (g ^ (commonPower P))⁻¹ • ((g ^ (commonPower P)) • (P.read x g U).part s) = _
    exact inv_smul_smul₀ (pow_ne_zero _ hg) _

include paid in
theorem input_colors (hg0 : g0 ≠ 0) (vacuum : ℝ → Config G n → ℝ)
    (hv : GradeAt 3 (Bulk.projected vacuum))
    (hG : ∀ g, GaugeInvariant (vacuum g))
    (hE : ∀ g, Envelope (vacuum g)) :
    InputColors (colors P vacuum) P where
  well := colors_well paid hg0 vacuum hv hG hE
  vacuum _ _ := rfl
  power _ _ := rfl
  marks := colors_markedLog paid hg0 vacuum


include paid in
/-- The complete original read, grouped by its unchanged finite set of powers. -/
theorem read_mode_sum (hg0 : g0 ≠ 0) (s : R.Mode) (hs : s ≠ R.quiet)
    (x : TestSpace D) (g : ℝ) (U : Config G n) :
    (P.read x g U).part s =
      ∑ z ∈ powers P, (g : ℂ) ^ z * NativePaidPacketSeries.value P s z x U :=
  read_mode paid hg0 s hs x g U

include paid in
/-- The exact cleared polynomial at every coupling, including zero. -/
theorem mark_polynomial_eq (hg0 : g0 ≠ 0) (vacuum : ℝ → Config G n → ℝ)
    (x : TestSpace D) (s : Hot R) (g : ℝ) (U : Config G n) :
    (colors P vacuum x).mark s g U =
      ∑ z ∈ powers P, (g ^ exponent P z) • NativePaidPacketSeries.value P s.val z x U :=
  mark_polynomial paid hg0 vacuum x s g U

end YM.Integration.NativePaidPacketColors
