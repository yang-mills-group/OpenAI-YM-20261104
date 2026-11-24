import YM.Integration.QLocalGradedVacuumLayers
import YM.Comparison.RG02.Bulk.Admits
import YM.Integration.NativeBoundedAtomSeries
import YM.Work.F05.Actions

/-!
The explicit analytic vacuum extension of the original finite layer list.
At zero coupling this is defined by its nonnegative powers, not by a
negative-power expression with division by zero. The same payload rows and
roots are retained. The relative rank condition is supplied by the reviewed graded output
class on this very list. Its availability is a separate qlocal projection
duty; it is not inferred from radial jets or from a different catalogue.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace YM.Integration.ActualGradedVacuum
open Function Filter Set Metric Lattice Wilson RG Precision Exterior
open IterationFour IterationFour.Vacuum
open LocalComparison.Global FullQLocal Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}

/-- The finite original list, with every full payload and root unchanged. -/
def restored (layers : List (Piece G n)) (g : ℝ) (U : Config G n) : ℝ :=
  (layers.map fun a => g ^ (a.power + 2 - a.rank) * unmaskedPayload a.packet U).sum

private theorem prefactor_nat (a : Piece G n) {g : ℝ} (hg : g ≠ 0)
    (ha : a.rank ≤ a.power + 2) :
    g ^ 2 * Render.prefactor g a = g ^ (a.power + 2 - a.rank) := by
  have he : (2 : ℤ) + Render.stepOrder a =
      ((a.power + 2 - a.rank : ℕ) : ℤ) := by
    unfold Render.stepOrder
    omega
  calc
    _ = g ^ ((2 : ℤ) + Render.stepOrder a) := by
      rw [Render.prefactor, zpow_add₀ hg, zpow_ofNat]
    _ = _ := by rw [he, zpow_natCast]

private theorem restored_eq_of_rank (layers : List (Piece G n)) {g : ℝ} (hg : g ≠ 0)
    (hrank : ∀ a ∈ layers, a.rank ≤ a.power + 2) (U : Config G n) :
    restored layers g U = g ^ 2 * unmaskedLayers layers g U := by
  revert hrank
  induction layers with
  | nil => intro hrank; simp [restored, unmaskedLayers]
  | cons a layers ih =>
      intro hrank
      have ha := hrank a (List.mem_cons_self ..)
      have hl : ∀ b ∈ layers, b.rank ≤ b.power + 2 :=
        fun b hb => hrank b (List.mem_cons_of_mem _ hb)
      change g ^ (a.power + 2 - a.rank) * unmaskedPayload a.packet U +
          restored layers g U =
        g ^ 2 * (Render.prefactor g a * unmaskedPayload a.packet U +
          unmaskedLayers layers g U)
      rw [mul_add, ← mul_assoc,
        prefactor_nat a hg ha, ih hl]

variable {layers : List (Piece G n)} {p : BudgetPoint}
variable {order rankCap : ℕ} {width budget : ℝ}
variable (H : GradedVacuumLayers layers p order rankCap width budget)

include H in
/-- Exact restoration of the unchanged full layer list at nonzero coupling. -/
theorem restored_eq {g : ℝ} (hg : g ≠ 0) (U : Config G n) :
    restored layers g U = g ^ 2 * unmaskedLayers layers g U :=
  restored_eq_of_rank layers hg H.leading_rank U

private theorem atom_budget (a : Piece G n) (ha : a ∈ layers) :
    Summable (fun i : ℕ => (H.packets.atom a i).budget width) := by
  let f (o : Site n) (i : ℕ) : ℝ :=
    if (a.packet.labels i).site = o then (H.packets.atom a i).budget width else 0
  have hs (o : Site n) : Summable (f o) := by
    simpa only [f, Atom.budget] using (H.packets.exponential a ha o).2.1
  have ht := summable_sum (s := Finset.univ) (fun o _ => hs o)
  convert ht using 1
  funext i
  simp [f]

private theorem payload_eq (a : Piece G n) (ha : a ∈ layers) (U : Config G n) :
    unmaskedPayload a.packet U =
      NativeBoundedAtomSeries.value (H.packets.atom a) (fun i => (a.packet.labels i).site) U := by
  exact tsum_congr fun i => H.packets.original_action a ha i U

include H in
theorem payload_grade (hwidth : 0 < width) (a : Piece G n)
    (ha : a ∈ layers) :
    GradeAt a.rank (fun A : fieldDir G n 1 => unmaskedPayload a.packet (represent A)) := by
  rw [show (fun A : fieldDir G n 1 => unmaskedPayload a.packet (represent A)) =
      (fun A => NativeBoundedAtomSeries.value
        (H.packets.atom a) (fun i => (a.packet.labels i).site) (represent A)) from
    funext fun A => payload_eq H a ha (represent A)]
  exact NativeBoundedAtomSeries.value_grade
    (H.packets.atom a) (fun i => (a.packet.labels i).site) hwidth
    (cap := a.rank) (fun _ => le_rfl) (atom_budget H a ha) (fun _ => le_rfl)

include H in
private theorem payload_gauge (a : Piece G n) (ha : a ∈ layers) :
    GaugeInvariant (unmaskedPayload a.packet) := by
  intro t U
  rw [payload_eq H a ha, payload_eq H a ha]
  apply tsum_congr
  intro i
  simp only [Atom.unmasked, Work.F05.slot_gauge]
  exact H.packets.invariant a ha i ..

include H in
private theorem payload_envelope (hwidth : 0 < width) (a : Piece G n)
    (ha : a ∈ layers) : Envelope (unmaskedPayload a.packet) := by
  rw [show unmaskedPayload a.packet =
      NativeBoundedAtomSeries.value (H.packets.atom a) (fun i => (a.packet.labels i).site) from
    funext (payload_eq H a ha)]
  have hb := atom_budget H a ha
  have hbound (i : ℕ) (U : Config G n) :
      ‖(H.packets.atom a i).unmasked U (a.packet.labels i).site‖ ≤
        (H.packets.atom a i).budget width * (2 : ℝ) ^ a.rank := by
    exact ((H.packets.atom a i).unmasked_bound U (a.packet.labels i).site).trans
      (mul_le_mul_of_nonneg_right ((H.packets.atom a i).lower_budget width hwidth) (by positivity))
  refine ⟨Measurable.tsum
      (fun i => ((H.packets.atom a i).unmasked_cont (a.packet.labels i).site).measurable),
    (∑' i, (H.packets.atom a i).budget width) * (2 : ℝ) ^ a.rank, fun U => ?_⟩
  have hn := (NativeBoundedAtomSeries.value_summable
    (H.packets.atom a) (fun i => (a.packet.labels i).site) hwidth
    (cap := a.rank) (fun _ => le_rfl) hb U).norm
  apply (norm_tsum_le_tsum_norm hn).trans
  exact (hn.tsum_le_tsum (fun i => hbound i U) (hb.mul_right _)).trans_eq
    tsum_mul_right

private theorem list_grade (k : ℕ) (l : List (Piece G n))
    (f : Piece G n → (ℝ × fieldDir G n 1) → ℝ)
    (h : ∀ a ∈ l, GradeAt k (f a)) :
    GradeAt k (fun y => (l.map fun a => f a y).sum) := by
  revert h
  induction l with
  | nil =>
      intro h
      simpa only [List.map_nil, List.sum_nil] using
        (GradeAt.grade_zero k : GradeAt k (0 : (ℝ × fieldDir G n 1) → ℝ))
  | cons a l ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      exact (h a (List.mem_cons_self ..)).add
          (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

include H in
theorem restored_grade (hwidth : 0 < width) :
    GradeAt 5 (Bulk.projected (restored layers)) := by
  change GradeAt 5 (fun y : ℝ × fieldDir G n 1 =>
    (layers.map fun a =>
      y.1 ^ (a.power + 2 - a.rank) * unmaskedPayload a.packet (represent y.2)).sum)
  apply list_grade
  intro a ha
  have hp := GradeAt.shifts (fun y : ℝ × fieldDir G n 1 => y.1)
    contDiffAt_fst rfl (a.power + 2 - a.rank)
  have hq := (payload_grade H hwidth a ha).coarse
    (g := fun y : ℝ × fieldDir G n 1 => y.2) contDiffAt_snd rfl
  have horder : 5 ≤ (a.power + 2 - a.rank) + a.rank := by
    have := (H.orders a ha).1
    have := H.leading_rank a ha
    omega
  simpa only [Function.comp_apply, smul_eq_mul] using (hp.scale hq).lower horder

include H in
theorem restored_gauge (g : ℝ) : GaugeInvariant (restored layers g) := by
  intro t U
  unfold restored
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  rw [payload_gauge H a ha t U]

private theorem list_envelope (l : List (Piece G n))
    (f : Piece G n → Config G n → ℝ)
    (h : ∀ a ∈ l, Envelope (f a)) :
    Envelope (fun U => (l.map fun a => f a U).sum) := by
  revert h
  induction l with
  | nil =>
      intro h
      simpa only [List.map_nil, List.sum_nil] using
        (Envelope.const (V := Config G n) 0)
  | cons a l ih =>
      intro h
      simpa only [List.map_cons, List.sum_cons] using
        (h a (List.mem_cons_self ..)).add
          (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

include H in
theorem restored_envelope (hwidth : 0 < width) (g : ℝ) :
    Envelope (restored layers g) := by
  apply list_envelope
  intro a ha
  exact (Envelope.const (g ^ (a.power + 2 - a.rank))).mul
    (payload_envelope H hwidth a ha)

include H in
/-- The exact same-list vacuum supplies the three native Colors receipts.
The physical action identity is retained on its nonzero-coupling domain. -/
theorem analytic_vacuum (hwidth : 0 < width) :
    GradeAt 5 (Bulk.projected (restored layers)) ∧
      (∀ g : ℝ, GaugeInvariant (restored layers g)) ∧
      (∀ g : ℝ, Envelope (restored layers g)) ∧
      (∀ g : ℝ, g ≠ 0 → ∀ U : Config G n,
        restored layers g U = g ^ 2 * unmaskedLayers layers g U) :=
  ⟨restored_grade H hwidth, restored_gauge H,
    restored_envelope H hwidth, fun _ hg U => restored_eq H hg U⟩

end YM.Integration.ActualGradedVacuum
end
