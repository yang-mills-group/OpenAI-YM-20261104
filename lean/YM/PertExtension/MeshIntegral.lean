import YM.PertExtension.Bins
import YM.PertExtension.GraphBudget

/-! Integrate pathwise separated convergence without discarding any power.
All positions supplied for all offsets in the same measurement. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.PertExtension.LatticePT.Grid
open MeasureTheory Filter Topology Set Finset Function Metric Lattice Extraction
open scoped Topology Classical BigOperators
variable {q:ℕ+}{n k:ℕ}(hq:1<q.val)
local notation "grid"=> offsets q n
local notation "reg"=> (Filter.atTop: Filter ℕ)

def stepper(t:ℕ)(f:grid t→ℝ)(p:Points n):ℝ:=∑ i:grid t, (deck q t i).indicator (fun z:Points n=>f i) p

lemma step_inside {v:grid k} {x:Points n}{f:grid k→ℝ}(hp:x∈deck q k v):stepper k f x=f v:=by
    unfold stepper; rw [Finset.sum_eq_single_of_mem v (Finset.mem_univ _) ?_, indicator_of_mem hp]; intro j _ hj
    exact indicator_of_notMem (fun he=> hj ((signal_eq q he).symm.trans (signal_eq q hp))) _
lemma step_missing {x:Points n}{f:grid k→ℝ}(h:∀ v:grid k,x∉deck q k v):stepper k f x=0:=sum_eq_zero fun j _=>indicator_of_notMem (h j) _
lemma finitely_charged {v:grid k}{f:grid k→ℝ}: Integrable ((deck q k v).indicator (fun z:Points n=>f v)):= IntegrableOn.integrable_indicator (integrableOn_const (by rw [deck,cell_volume (epsilon_pos q k)];exact ENNReal.ofReal_ne_top)) (deck_meas ..)
lemma charged (f:grid k→ℝ):Integrable (stepper k f):= integrable_finsetSum _ (fun i hi=>by exact finitely_charged)
lemma knot (f:grid k→ℝ): (∫ x,stepper k f x)=epsilon q k ^(4*n) * (∑ i,f i) := by
    unfold stepper;rw [MeasureTheory.integral_finsetSum _ (fun _ _=>finitely_charged), Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi=> by rw [MeasureTheory.integral_indicator (deck_meas ..),MeasureTheory.setIntegral_const,deck_volume];rfl -- check

variable {K:Set (Points n)}{T:Points n→ℝ}{F:∀ m,offsets q n m → ℝ}
variable (h:∀ (s:(m:ℕ) → offsets q n m) x, x∈K → Tendsto (fun m=>sample q m (s m)) reg (𝓝 x) → Tendsto (fun m=> F m (s m)) reg (𝓝 (T x)))
include h hq
lemma roof (hK : IsCompact K) : ∃ C≥0,∀ᶠ k:ℕ in atTop, ∀ i:grid k,sample q k i∈K → |F k i|≤C:=GraphBudget.wallet hK (fun x hx=>⟨(fun m=> signal q m x),choose_sample hq x⟩) h

-- F itself includes actual shape test in this comparison
-- Thus exact zeros on omitted mesh sites, including possibly for shapes near diagonals.

theorem integrable_spots (hK : IsCompact K)(hFin:∀ k s,sample q k s∉K → F k s=0) (hInf:∀ y∉K,T y=0) : Integrable T ∧ Tendsto (fun k=>epsilon q k^(4*n) * ∑ i,F k i) reg (𝓝 (∫ x:Points n,T x)) := by
    obtain ⟨C,hC,H⟩:= roof hq h hK
    obtain ⟨R,hR⟩:= hK.isBounded.subset_closedBall (0:Points n)
    let A:= fun m=>stepper m (F m)
    have hA : ∀ m,Integrable (A m):=fun m=> charged _
    let L := closedBall (0:Points n) (R+1); have hL : IsCompact L:=isCompact_closedBall ..
    let price := L.indicator (fun _=> C); have hP : Integrable price :=(integrableOn_const hL.measure_ne_top).integrable_indicator hL.measurableSet
    have hh:Tendsto (fun k=>(4*n:ℝ)*epsilon q k) reg (𝓝 0):=by simpa only [mul_zero] using! ((epsilon_zero hq).mono_right inf_le_left).const_mul (4*n : ℝ)
    have ht:∀ᶠ k:ℕ in reg, ∀ x:Points n, ‖A k x‖ ≤ price x:= by
      filter_upwards [H,hh.eventually (gt_mem_nhds (show (0:ℝ)<1 from zero_lt_one))] with k hk hZ x
      by_cases hI:∃ i:grid k,x∈deck q k i
      · obtain ⟨i,hi⟩:=hI; rw [show A k x=F k i from step_inside hi]
        by_cases hx:sample q k i ∈ K
        · unfold price;rw [indicator_of_mem (a:=x) ?_]; apply hk _ hx
          unfold L; change dist x 0 ≤ _
          linarith only [show (4*n:ℝ) * epsilon q k<1 from hZ,show dist (sample q k i) 0 ≤ R from hR hx, dist_triangle_right x (0:Points n) (sample q k i),deck_dist q hi, dist_comm x (sample q k i),dist_comm (0:Points n) (sample q k i)]
        rw [hFin _ _ hx,norm_zero]; unfold price;by_cases x∈L <;> simp [*,hC]
      have hz : A k x=0:=step_missing (by simpa using! hI)
      rw [hz,norm_zero];unfold price;by_cases x∈L <;> simp [*,hC]
    have hLimit x : Tendsto (fun k=>A k x) reg (𝓝 (T x)):=by
      let b k:= signal q k x
      by_cases hx:x∈K
      · have ht: Tendsto (fun k=> F k (b k)) reg (𝓝 (T x)):= h b x hx (choose_sample hq x)
        exact ht.congr' <| (valid hq x).mono fun k hk=> (step_inside (f:=F k) hk).symm
      apply tendsto_const_nhds.congr'
      filter_upwards [valid hq x, (choose_sample hq x).eventually (hK.isClosed.isOpen_compl.mem_nhds hx)] with k hk hZ;dsimp only [A];rw [step_inside hk,hFin k _ hZ,hInf x hx]
    constructor
    · refine hP.mono' (aestronglyMeasurable_of_tendsto_ae (β:=ℝ) atTop (fun m=> (hA m).aestronglyMeasurable) (Eventually.of_forall hLimit)) <| Eventually.of_forall fun x=>?_ -- adjust
      exact le_of_tendsto (hLimit x).norm (ht.mono fun k hk=> hk x)
    simp_rw [← knot]
    exact tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall (fun i=>(hA i).aestronglyMeasurable)) (ht.mono fun i hi=>Eventually.of_forall hi) hP (Eventually.of_forall hLimit)
end YM.PertExtension.LatticePT.Grid
