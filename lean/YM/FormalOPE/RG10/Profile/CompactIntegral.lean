import YM.FormalOPE.RG10.Profile.BoundedTail
import YM.PertExtension.MeshIntegral
/-!
# Near-lattice sums of smooth-profile slices in smooth topology (fixed support)
Basic quadrature extended for Banach-valued families via anchored Grid tile laws
and scalar-step properties.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.FormalOPE.RG10.Profile
open Function Set MeasureTheory Filter Topology Metric Finset Extraction
open PertExtension.LatticePT Grid
open scoped Topology ContDiff Classical BigOperators ENNReal
variable {n : ℕ} {q : ℕ+}(hq:1<q.val) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
local notation "X" => Points n
local notation "σ" => Grid.sample q
variable (f : Points n → F) (hf : Continuous f) (hx : HasCompactSupport f)
include hf hx hq
-- Instead of needing Banach-valued `GraphBudget.wallet`, apply
-- dominated convergence using scalar stepper on the norm.
theorem weighted : Tendsto (fun m=> epsilon q m ^ (4*n) • ∑ i, f (σ m i))
    atTop (𝓝 (∫ x, f x)) := by
 let step k (x:X) := ∑ i:offsets q n k, (Grid.deck q k i).indicator (fun _=> f (σ k i)) x
 have he {k} {x:X} {i:offsets q n k} (h:x∈Grid.deck q k i) : step k x=f (σ k i) := by
    unfold step; rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) ?_, indicator_of_mem h]; intro j _ hj; exact indicator_of_notMem (fun he=> hj ((signal_eq q he).symm.trans (signal_eq q h))) _
 have ht k i: Integrable ((Grid.deck q k i).indicator (fun _=> f (σ k i))) := IntegrableOn.integrable_indicator (integrableOn_const (by rw [Grid.deck, cell_volume (epsilon_pos q k)]; exact ENNReal.ofReal_ne_top)) (deck_meas ..)
 have hi (k:ℕ): Integrable (step k):= integrable_finsetSum _ (fun p _=> ht k p)
 have hz (k:ℕ) x : ‖step k x‖ = Grid.stepper k (fun i=> ‖f (σ k i)‖) x:= by
    by_cases h: ∃ i:offsets q n k, x∈Grid.deck q k i 
    · obtain ⟨i,h⟩ := h; rw [he h,step_inside h]
    push Not at h
    rw [show step k x=0 from sum_eq_zero fun i _=>indicator_of_notMem (h i) _, norm_zero, step_missing h]
 have hlim x : Tendsto (fun k=>step k x) atTop (𝓝 (f x)):= ((hf.tendsto x).comp (choose_sample hq x)).congr' ((valid hq x).mono fun _ h=>(he h).symm)
 let K:= tsupport f
 have hN x (H:x∉K) : f x=0:= image_eq_zero_of_notMem_tsupport H
 obtain ⟨R,hR⟩:= hx.isBounded.subset_closedBall (0:X)
 let L:= closedBall (0:X) (R+1)
 have hL : IsCompact L:= isCompact_closedBall ..
 obtain ⟨M,hM⟩:= hf.bounded_above_of_compact_support hx
 let bound := L.indicator fun _ => M
 have hnk : 0 ≤ M:= (norm_nonneg _).trans (hM (0:X))
 have hn : Integrable bound:= (integrableOn_const hL.measure_ne_top).integrable_indicator hL.measurableSet
 have hε : Tendsto (fun k=> (4*n:ℝ)*epsilon q k) atTop (𝓝 0) := by simpa only [mul_zero] using! ((epsilon_zero hq).mono_right inf_le_left).const_mul (4*n:ℝ)
 have hh : ∀ᶠ k in atTop, ∀ x, ‖step k x‖ ≤ bound x := by
    filter_upwards [hε.eventually (gt_mem_nhds (show (0:ℝ)<1 from zero_lt_one))] with k h x
    have hb : 0 ≤ bound x := by unfold bound; by_cases hi:x∈L <;> simp [hnk,hi]
    by_cases H: ∃ i:offsets q n k,x∈Grid.deck q k i
    · obtain ⟨i,H⟩:=H; rw [he H]; by_cases hu:(σ k i)∈K
      · unfold bound; rw [indicator_of_mem (a:=x) ?_]; apply hM
        change dist x 0 ≤ R + 1; calc
          _ ≤ dist x (σ k i) + dist (σ k i) 0:= dist_triangle ..
          _ ≤ 1+R:= add_le_add (by rw [dist_comm]; exact le_trans (deck_dist q H) (show (4*n:ℝ)*epsilon q k < 1 from h).le) (hR hu)
          _ = _:= add_comm ..
      rwa [hN _ hu,norm_zero]
    rw [hz,step_missing (by simpa using! H)]; exact hb
 have hW : ∀ k:ℕ, (∫ x, step k x)=epsilon q k ^ (4*n) • ∑ i,f (σ k i):=by
    intro k; unfold step; rw [MeasureTheory.integral_finsetSum _ (fun i _=> ht k i), Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> by rw [integral_indicator (deck_meas ..),MeasureTheory.setIntegral_const,deck_volume]
 simp_rw [← hW]; exact tendsto_integral_filter_of_dominated_convergence bound (Eventually.of_forall (fun k=> (hi k).aestronglyMeasurable)) (hh.mono (fun k h=> Eventually.of_forall h)) hn (Eventually.of_forall hlim)
end YM.FormalOPE.RG10.Profile
