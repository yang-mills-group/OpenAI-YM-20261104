import YM.PhysMS.Frame.Stage
import YM.PhysMS.Frame.Phases
import YM.Pert.FirstTarget
import YM.TraceExtension.Pith.Orders
import YM.TraceExtension.Endpoint

/-! All positive lengths on the same Wilson hierarchy. -/
set_option autoImplicit false
noncomputable section
namespace YM.AllRadiiMaxwell
open Function Filter Set Spec Climb OPE OPE.Orbits PhysMS PhysMS.Frame Trace Trace.Pilot
open Trace.Pith Table Next.UVStress TraceExtension
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (simple : G.Simple)
variable (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

private theorem unit_term (H : (Bel C.book).Hierarchy) {s a d e : ℝ} (P : Spin.change S 4)
    (angle : AlignV F.room.kernel F.sector H P) (m : Measures F s P a d e) :
    (4 : ℝ) • (e : ℂ) = s^4 • expectation S 4 (stressTrace F.sector.energy) := by
  let v := stressTrace F.sector.energy
  have form : P.symm (s^4 • v) =
      (4:ℝ) • (d • stepField C + e • (Bel C.book).unit 4) := by
    calc
      _ = ∑ k : Axis, (a • standard4 C k k + (d • stepField C + e • (Bel C.book).unit 4)) := by
        unfold v stressTrace
        rw [Finset.smul_sum, map_sum]
        apply Finset.sum_congr rfl
        intro k _
        simpa [Trace.Pith.erase, add_assoc] using m.reads k k
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.smul_sum, trace_none, smul_zero, zero_add,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        norm_cast
  let E := (expectation (Bel C.book) 4).restrictScalars ℝ
  have val := congrArg E form
  have vev : E (P.symm (s^4 • v)) = s^4 • expectation S 4 v := by
    change expectation (Bel C.book) 4 _ = _
    rw [← angle.cent, P.apply_symm_apply]
    exact ((expectation S 4).restrictScalars ℝ).map_smul ..
  rw [vev, map_smul, map_add, map_smul, map_smul,
    show E (stepField C) = 0 from sceneV H,
    show E ((Bel C.book).unit 4) = 1 from mean_unit H.laws,smul_zero,zero_add] at val
  simpa using val.symm


private theorem stress_column {U : ℝ → tower S} (H : (Bel C.book).Hierarchy)
    {Z : Trace.Terrace.Arch C} {l : Ultrafilter (ℕ × ℕ)} (bliss : Bliss F l Z H)
    (angle : PlotX F H l simple (fun r => U r 4))
    (choresU : ∀ m, ∀ᶠ r in trail, chores r (U r 4) m) (i j : Axis) :
    Tendsto (fun r : ℝ => (U r 4).symm (r^4 • F.sector.energy i j))
      trail (𝓝 (Pert.freeStress C.labels i j)) := by
  have coupling := wilson_link F simple bliss.budgets bliss.keen bliss.lies
  obtain ⟨d, hd⟩ := margaret F simple bliss (fun r => U r 4) angle
  obtain ⟨a, e, hm, ha, _, _⟩ := formed H F simple coupling hd angle choresU
  have small := postd H F simple coupling hd angle
  have e4 : Tendsto (fun r : ℝ => (4:ℝ) • (e r : ℂ)) trail (𝓝 0) := by
    have z : Tendsto (fun r : ℝ => r^4 • expectation S 4 (stressTrace F.sector.energy))
        trail (𝓝 0) := by
      have hr : Tendsto (fun r : ℝ => r) trail (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using (hr.pow 4).smul_const
        (expectation S 4 (stressTrace F.sector.energy))
    apply z.congr'
    filter_upwards [angle, hm] with r hi hme
    exact (unit_term F H (U r 4) hi.1.frame hme).symm
  have ec : Tendsto (fun r : ℝ => (e r : ℂ)) trail (𝓝 0) := by
    simpa [smul_smul, inv_mul_cancel₀ (by norm_num : (4:ℝ) ≠ 0)] using e4.const_smul (4:ℝ)⁻¹
  have er : Tendsto e trail (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_re, Complex.zero_re] using (Complex.continuous_re.tendsto (0:ℂ)).comp ec
  have name : standard4 C = Pert.freeStress C.labels := by
    rw [show standard4 C = _ from Trace.Over.canonical_meter (C := C)]
    change UVNext.FreeStress.torch C.labels (-1) = -Maxwell.Free.original C.labels
    rw [← Pert.common_stress, UVNext.FreeStress.torch, UVNext.FreeStress.torch, neg_one_smul, one_smul]
  rw [← name]
  have lim := ((ha.smul_const (standard4 C i j)).add
    (small.smul_const (erase (C:=C) (stepField C) i j))).add
      (er.smul_const (erase (C:=C) ((Bel C.book).unit 4) i j))
  simpa only [one_smul, zero_smul, add_zero] using
    lim.congr' (hm.mono fun r he => (he.reads i j).symm)

/-- A single frame at all real radii, its fixed Ward stress, and mixed jets
for every insertion whose coordinates converge in that frame. -/
def Law (U : ℝ → tower S) : Prop :=
    Leading F U ∧
      (∀ i j, Tendsto (fun r : ℝ => (U r 4).symm (r^4 • F.sector.energy i j))
        trail (𝓝 (Pert.freeStress C.labels i j))) ∧
      ∀ {n : ℕ} (d : Caps n) (u : ℝ → (i : Fin n) → S.Field (d i)) (v : MaxwellSlots C d),
        (∀ i, Tendsto (fun r => (U r (d i)).symm (u r i)) trail (𝓝 (v i))) →
        ∀ (j : ℕ) (K : Set (Points n)), IsCompact K → K ⊆ conf n →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ r in trail, ∀ x ∈ K, ∀ p : Viewers F,
          ‖iteratedFDeriv ℝ j (fun y => S.classMoment (spectator F p) d (r • y) (u r)) x -
            iteratedFDeriv ℝ j (WickGoal v) x‖ < ε

theorem allRadii (X : Scaling S) (foundation : Foundation F Q)
    (trace : Trace.Target.Result.{0} F simple) : ∃ U, Law F U := by
  obtain ⟨H, Z, l, bliss, _⟩ := trace.stress
  obtain ⟨U, angle, choresU, lead, _⟩ := base_stage simple F H bliss
  refine ⟨U, lead, stress_column F simple H bliss angle choresU, ?_⟩
  intro n d u v hu j K compact sep ε pos
  let w (r : ℝ) (i : Fin n) := (U r (d i)).symm (u r i)
  have along (p : ℝ → Viewers F) :
      TendstoUniformlyOn (fun r => iteratedFDeriv ℝ j (measured F (p r) (U r) (w r) r))
        (iteratedFDeriv ℝ j (WickGoal v)) trail K := by
    apply measured_tensor F (self_mem_nhdsWithin : ∀ᶠ r in trail, 0 < r)
      d j (fun i => Module.finBasis ℂ ((Bel C.book).Field (d i))) compact sep _ hu
    intro b
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [all_leading F Q U lead simple X foundation j
      (fun i => Module.finBasis ℂ ((Bel C.book).Field (d i)) (b i)) K compact sep δ hδ] with r h x hx
    rw [dist_comm, dist_eq_norm]
    exact h x hx (p r)
  have every := universalize (p := fun r (p : Viewers F) => ∀ x ∈ K,
    ‖iteratedFDeriv ℝ j (measured F p (U r) (w r) r) x -
      iteratedFDeriv ℝ j (WickGoal v) x‖ < ε) (fun p =>
    (Metric.tendstoUniformlyOn_iff.mp (along p) ε pos).mono fun r h x hx => by
      simpa only [dist_comm (iteratedFDeriv ℝ j (WickGoal v) x), dist_eq_norm] using h x hx)
  filter_upwards [every] with r h x hx p
  have eqn : measured F p (U r) (w r) r =
      fun y => S.classMoment (spectator F p) d (r • y) (u r) := by
    funext y
    unfold PhysMS.measured
    simp only [w, LinearEquiv.apply_symm_apply]
  simpa only [eqn] using h p x hx


/-- Each slot is either a free-field label in the running frame or a named
component of the physical Ward tensor. -/
abbrev Slot (C : Family G) := (Bel C.book).Tag ⊕ (Axis × Axis)

def cap : Slot C → ℕ
  | .inl q => q.1
  | .inr _ => 4

def wickSlot : (s : Slot C) → (Bel C.book).Field (cap s)
  | .inl q => q.2
  | .inr ij => Pert.freeStress C.labels ij.1 ij.2

def ymSlot (U : ℝ → tower S) (r : ℝ) : (s : Slot C) → S.Field (cap s)
  | .inl q => U r q.1 q.2
  | .inr ij => r^4 • F.sector.energy ij.1 ij.2

/-- The uniform, all-phase, marked Maxwell test with a real radius. -/
theorem Law.marked {U : ℝ → tower S} (h : Law F U) {n : ℕ} (q : Fin n → Slot C)
    (j : ℕ) (K : Set (Points n)) (compact : IsCompact K) (sep : K ⊆ conf n)
    (ε : ℝ) (pos : 0 < ε) : ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ x ∈ K, ∀ p : Viewers F,
    ‖iteratedFDeriv ℝ j (fun y => S.classMoment (spectator F p) (cap ∘ q)
        (r • y) (fun i => ymSlot F U r (q i))) x -
      iteratedFDeriv ℝ j (WickGoal (fun i => wickSlot (q i))) x‖ < ε := by
  have column (s : Slot C) : Tendsto (fun r => (U r (cap s)).symm (ymSlot F U r s))
      trail (𝓝 (wickSlot s)) := by
    cases s with
    | inl v =>
      exact (tendsto_const_nhds (f := trail) (x := v.2)).congr
        (fun r => ((U r v.1).symm_apply_apply v.2).symm)
    | inr ij => exact h.2.1 ij.1 ij.2
  exact h.2.2 (cap ∘ q) (fun r i => ymSlot F U r (q i)) (fun i => wickSlot (q i))
    (fun i => column (q i)) j K compact sep ε pos

end YM.AllRadiiMaxwell
