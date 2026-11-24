import YM.Integration.WilsonSharpPhysicalTreeDetectorResponse
import YM.OPE.Logarithmic

/-! A single exponent and root-radius threshold for the actual finite detector
family. Rotating positions retain their original clearance. Moving labels are
already contracted against their complete fixed bases in the reader. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeDetectorSweep
open Function Filter Set MeasureTheory Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader
open OPE.Prescription OPE.Arboreal OPE.Arboreal.Mountain
open WilsonCenteredNestedShadowBasis WilsonSharpPhysicalTreeDetectorKernel WilsonSharpPhysicalTreeDetectorResponse
open scoped Classical Topology BigOperators
attribute [local instance] YM.Work.A15.compact_ortho
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {I J : Type} [Fintype I] [Fintype J]

/-- All locations in one detector orbit have one strictly positive clearance, also for the empty exterior. -/
lemma clearance (e : Exterior C.book) : ∃ c : ℝ, 0 < c ∧ ∀ (k : Ortho) (o : E4), ClearOf o (swung e k o) c := by
  have inj := beside_distinct.mp (bearing_clear e)
  have small {z : ℝ} (hz : 0 < z) : ∀ᶠ r : ℝ in 𝓝[>]0, r ≤ z :=
    (ge_mem_nhds hz).filter_mono nhdsWithin_le_nhds
  have off (j : Fin e.n) : ∀ᶠ r : ℝ in 𝓝[>]0, r ≤ ‖bearing e j‖ :=
    small (norm_pos_iff.mpr (Ne.symm (inj.2.2 () j)))
  have pair (i j : Fin e.n) : ∀ᶠ r : ℝ in 𝓝[>]0, i ≠ j → r ≤ ‖bearing e i - bearing e j‖ := by
    by_cases ne : i = j
    · exact Eventually.of_forall fun _ h => (h ne).elim
    · exact (small (norm_pos_iff.mpr (sub_ne_zero.mpr (inj.2.1.ne ne)))).mono fun _ hr _ => hr
  obtain ⟨c,hc,ho,hp⟩ := ((show ∀ᶠ r : ℝ in 𝓝[>]0, 0 < r from self_mem_nhdsWithin).and
    ((eventually_all.mpr off).and (eventually_all.mpr fun i => eventually_all.mpr (pair i)))).exists
  refine ⟨c,hc,fun k o => ⟨fun j => ?_,fun i j ne => ?_⟩⟩
  · change c ≤ ‖o - (o + Ortho.move k (bearing e j))‖
    rw [show o - (o + Ortho.move k (bearing e j)) = - Ortho.move k (bearing e j) from by abel,norm_neg,Ortho.move_norm]
    exact ho j
  · change c ≤ ‖(o + Ortho.move k (bearing e i)) - (o + Ortho.move k (bearing e j))‖
    rw [add_sub_add_left_eq_sub]
    change c ≤ ‖Ortho.motion k (bearing e i) - Ortho.motion k (bearing e j)‖
    rw [←map_sub]
    change c ≤ ‖Ortho.move k (bearing e i-bearing e j)‖
    rw [Ortho.move_norm]
    exact hp i j ne

lemma orbit (trace : LogTrace F Q.port) (s : Arboreal I) (p : I → C.book.Token) (h : ℕ)
    (e : Exterior C.book) (w : Labels S (expo e)) {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η) :
    ∃ b : ℕ, ∀ᶠ r : ℝ in 𝓝[>]0, ∀ (x : I→E4) (t : I→ℝ), t s.root = r → s.Convoy M η t x →
      ∀ k, b ≤ k → ∀ u : Ortho, LogError F s Q.port p (names w) h x t (swung e u (x s.root)) k := by
  obtain ⟨c,hc,apart⟩ := clearance (C:=C) e
  obtain ⟨b,rows⟩ := trace.testing s p (names w) h M η c hM hη hc
  refine ⟨b,?_⟩
  filter_upwards [rows] with r row x t rt fit k bk u
  exact row x t _ rt fit (apart u _) k bk

lemma raw (s : Arboreal I) (p : I→C.book.Token) {d : (↑s.leaves : Type)→ℕ} (v : Labels S d)
    (hp : crop p s.leaves = names v) {g : J→ℕ} (w : Labels S g) (h : ℕ)
    {x : I→E4} {t : I→ℝ} {y : J→E4} {k : ℕ} (row : LogError F s Q.port p (names w) h x t y k)
    (q : Viewers F) : ‖discrepancy (spectator F q) h (crop x s.leaves) (x s.root) v
      (shadowOld Q.port h (crop x s.leaves) (x s.root) v) y w‖ ≤ s.listPrice p t (h+1) k := by
  rw [discrepancy_old Q.port h _ _ _ _ _ (spectate F q) (spectate_respects F q) (spectate_ready F q) row.apertures]
  simpa only [← hp] using row.ready.phaseBound q

lemma price_nonneg (s : Arboreal I) (p : I→C.book.Token) {t : I→ℝ} (n k : ℕ)
    (fit : s.Graduated t) (small : 1 ≤ run (t s.root)) : 0 ≤ s.listPrice p t n k := by
  have hr := fit.reputation small
  exact mul_nonneg (fit.worth n p s.initial).le (pow_nonneg ((zero_le_one.trans hr.1).trans hr.2) _)

/-- The original raw sharp tree theorem on every rotating detector basis orbit,
with its exponent and threshold chosen before every admitted radius array. -/
theorem original (trace : LogTrace F Q.port) (s : Arboreal I) (p : I→C.book.Token) (h : ℕ)
    {d : (↑s.leaves : Type)→ℕ} (v : Labels S d) (hp : crop p s.leaves = names v)
    {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η) :
    ∃ b : ℕ, ∀ᶠ r : ℝ in 𝓝[>]0, ∀ (x : I→E4) (t : I→ℝ), t s.root = r → s.Convoy M η t x →
      ∀ k, b ≤ k → Good F Q h (crop x s.leaves) (x s.root) ∧
        ‖response F Q h (crop x s.leaves) v (x s.root) - insertion F Q h (x s.root)
          (shadowOld Q.port h (crop x s.leaves) (x s.root) v)‖ ≤ s.listPrice p t (h+1) k := by
  choose bs hs using fun a : Site F Q h => orbit F Q trace s p h a.2.2.val (0 : Labels S (expo a.2.2.val)) hM hη
  choose bp hp' using fun a : Probe F Q h => orbit F Q trace s p h a.2.2.1.val (axis S _ a.2.2.2) hM hη
  let b := (∑ a,bs a) + (∑ a,bp a)
  have siteMax (a : Site F Q h) : bs a ≤ b := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)).trans (Nat.le_add_right _ _)
  have probeMax (a : Probe F Q h) : bp a ≤ b := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)).trans (Nat.le_add_left _ _)
  refine ⟨b,?_⟩
  filter_upwards [eventually_all.mpr hs,eventually_all.mpr hp',
    (run_towards (tendsto_id : Tendsto (fun r:ℝ => r) (𝓝[>]0) (𝓝[>]0))).eventually_ge_atTop 1] with r sites probes small x t rt fit k bk
  have ok : Good F Q h (crop x s.leaves) (x s.root) := fun a u => (sites a x t rt fit k ((siteMax a).trans bk) u).right
  refine ⟨ok,?_⟩
  have pn := price_nonneg s p (h+1) k fit.sizes (rt ▸ small)
  apply (pi_norm_le_iff_of_nonneg pn).2
  intro a
  apply (ContinuousMap.norm_le _ pn).2
  intro u
  change ‖response F Q h (crop x s.leaves) v (x s.root) a u - response F Q h (sole (x s.root))
    (sole (shadowOld Q.port h (crop x s.leaves) (x s.root) v) : Labels S (fun _:Unit => h)) (x s.root) a u‖ ≤ _
  rw [response_apply F Q _ _ _ _ ok,response_apply F Q _ _ _ _ (centerGood F Q h _)]
  exact raw F Q s p v hp (axis S _ a.2.2.2) h (probes a x t rt fit k ((probeMax a).trans bk) u) none

end YM.Integration.WilsonSharpPhysicalTreeDetectorSweep
