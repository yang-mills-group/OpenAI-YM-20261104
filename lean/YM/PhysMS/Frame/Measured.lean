import YM.TraceExtension.Atlas.Sink
import YM.OPE.Eye.Views
import YM.OPE.Levy.Panel

/-! # Accuracy interface for all-length comparison at leading order

No rate built into Leading. Same tower before tests, eventually commutes
with the inclusions through every fixed truncation. H (signed-axis permutation) and complex
conjugation, as in Trace. Operator and coupling conversion not built into these data. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysMS
open Function Filter Set Spec Trace.Pilot OPE OPE.Orbits
open Climb Spin Next.UVStress
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S)

abbrev tower (S : Table C.book) := ∀ d : ℕ, change S d

abbrev MaxwellSlots (C : Family G) {n} (d : Caps n) := ∀ i,(Bel C.book).Field (d i)

def measured (p : Viewers F) (J : tower S) {n} {d : Caps n}
    (v : MaxwellSlots C d) (r : ℝ) (x : Points n) :=
    S.classMoment (spectator F p) d (r • x) (fun i=> J (d i) (v i))

def WickGoal {C : Family G} {n} {d : Caps n} (v : MaxwellSlots C d) (x : Points n) :=
    (Bel C.book).classMoment (Bel C.book) d x v

structure Leading (J : ℝ → tower S) : Prop where
    equivariant (d) : ∀ᶠ r in trail, realH F.room.kernel.spin (Maxwell.Free.spin_free C.labels) (J r d)
    raised {d e} (h : d ≤ e) : ∀ᶠ r in trail, ∀ v, J r e ((Maxwell.Free.scheme C.labels).rise h v) = F.sector.derivatives.rise h (J r d v)
    unit (d) : ∀ᶠ r in trail, J r d ((Bel C.book).unit d) = S.unit d
    lead (n : ℕ) (d : Caps n) (v : MaxwellSlots C d) (j : ℕ) (K : Set (Points n)) : IsCompact K → K ⊆ conf n →
      TendstoUniformlyOn (fun r=> iteratedFDeriv ℝ j (measured F none (J r) v r))
        (iteratedFDeriv ℝ j (WickGoal v)) trail K

lemma WickGoal_tied {n} {d : Caps n} (v : MaxwellSlots C d) {x : Points n} (hx : x∈conf n) :
    ContDiffAt ℝ ∞ (WickGoal v) x :=
  ((Bel C.book).class_smooth (Bel C.book) (Maxwell.table_smooth C.labels)
    (fun i => ⟨d i,v i⟩)).contDiffAt ((conf_open _).mem_nhds hx)

lemma leading_at {J : ℝ → tower S} (H : Leading F J) {n : ℕ} {d : Caps n} (v : MaxwellSlots C d)
    {I : Type*} {l : Filter I} {r : I → ℝ} (hr : Tendsto r l trail) {x : I → Points n} {y}
    (hx : Tendsto x l (𝓝 y)) (hy : y ∈ conf n) :
    Tendsto (fun i=>measured F none (J (r i)) v (r i) (x i)) l (𝓝 (WickGoal v y)) := by
  let E := fun i: I => measured F none (J (r i)) v (r i) (x i)-WickGoal v (x i)
  have hp : Tendsto E l (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr; intro ε he
    obtain ⟨s,hA,hB,hC⟩:= LocallyCompactSpace.local_compact_nhds y _ ((conf_open n).mem_nhds hy)
    have hz := H.lead n d v 0 s ?_ ?_ <;> first| assumption | skip
    filter_upwards [hr.eventually (Metric.tendstoUniformlyOn_iff.mp hz ε he),hx.eventually hA] with i hi hu
    specialize hi (x i) hu
    rw [dist_comm,dist_eq_norm] at hi
    change dist (measured F none (J _) v _ _-_) 0 < _
    rw [dist_zero_right]
    apply lt_of_le_of_lt ?_ hi
    apply le_of_eq; rw [show iteratedFDeriv ℝ 0 (measured F none (J (r i)) v (r i)) (x i) - iteratedFDeriv ℝ 0 (WickGoal v) (x i) = iteratedFDeriv ℝ 0 (measured F none (J (r i)) v (r i) - WickGoal v) (x i) from ?_,norm_iteratedFDeriv_zero]
    swap
    · ext z; simp
    rfl
  exact Tendsto.congr' (Eventually.of_forall fun _=> sub_add_cancel ..) (by
    simpa only [zero_add] using! hp.add ((WickGoal_tied v hy).continuousAt.tendsto.comp hx))
end YM.PhysMS
