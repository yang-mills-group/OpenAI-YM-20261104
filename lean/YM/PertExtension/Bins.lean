import YM.PertExtension.AirLimits
import YM.Extraction.Round

/-! Riemann tiles at a changing even inversion-orbit period, identified
with the exact native representatives on any fixed compact region eventually. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.PertExtension.LatticePT.Grid
open MeasureTheory Filter Topology Set Finset Function Metric Lattice Extraction
open scoped Real NNReal ENNReal ContDiff BigOperators Classical Topology
variable (q:ℕ+) {n:ℕ}
abbrev offsets (n:ℕ)(k:ℕ):=Fin n→Native q k
def sample (k:ℕ)(x:offsets q n k):Points n:=Extraction.tag (epsilon q k) (Lattice.lift ∘ x)
lemma sample_eq (k:ℕ)(x:offsets q n k) : sample q k x = points (point q k ∘ x):=rfl

abbrev deck(k:ℕ)(x:offsets q n k):Set (Points n):=Extraction.segment (epsilon q k) (Lattice.lift ∘ x)
def signal (k:ℕ)(x:Points n):offsets q n k:=wrap _ ∘ Extraction.address (epsilon q k) x
lemma signal_eq {k:ℕ} {x:offsets q n k}{p:Points n}(hp:p∈deck q k x): signal q k p=x := by
  change Extraction.address _ _ = _ at hp
  exact funext fun i=> by change wrap _ (Extraction.address _ _ _)=_; rw [hp, Function.comp_apply, Lattice.wrap_lift (x i)]
lemma deck_meas (k:ℕ)(x:offsets q n k):MeasurableSet (deck q k x):=Extraction.measurable_segment (epsilon_pos q k) _
lemma deck_volume (k:ℕ)(x:offsets q n k): volume.real (deck q k x)=epsilon q k^(4*n):=by
   unfold Measure.real; rw [Extraction.cell_volume (epsilon_pos q k), ENNReal.toReal_ofReal (pow_nonneg (epsilon_pos q k).le _)]
lemma deck_dist {k:ℕ} {x:offsets q n k}{p:Points n}(hp:p∈ deck q k x): dist (sample q k x) p ≤4*n*epsilon q k:= by
    have h:=Extraction.approximate (epsilon_pos q k) p
    change Extraction.address _ _= _ at hp; rw [hp] at h;exact h

variable {q} (hq:1<q.val)
include hq
lemma valid (x:Points n): ∀ᶠ k in atTop, x∈ deck q k (signal q k x) := by
   let c := Extraction.address (n:=n)
   have he i j : ∀ᶠ k in atTop,-((side q k).val:ℤ)<2*c (epsilon q k) x i j ∧ 2*c (epsilon q k) x i j≤ ((side q k).val:ℤ):=by
        let d:ℕ→ℝ:= epsilon q
        let a k:= c (d k) x i j
        have ht (k:ℕ) : ‖(a k:ℝ)‖ ≤ magnify q k*(|x i j|+d k):=by
           suffices |(a k:ℝ)| ≤ (|x i j|+d k)/d k by simpa only [div_eq_inv_mul,d,epsilon,inv_inv,Real.norm_eq_abs] using! this
           apply (le_div_iff₀ (epsilon_pos q k)).mpr
           have hgrid := coord_grid_bound (n:=n) (epsilon_pos q k) x i j
           rw [← abs_of_pos (epsilon_pos q k),← abs_mul]; change |(a k:ℝ)*d k|≤_; rw [mul_comm ((a k:ℝ))]
           have he:= abs_add_le (d k*(a k)-x i j) (x i j)
           rw [sub_add_cancel] at he
           linarith only [show |d k * ↑(a k) - x i j| ≤d k from hgrid,he]
        have hl:Tendsto (fun k=> |(a k:ℝ)|/((side q k).val:ℝ)) atTop (𝓝 0):=by
            apply squeeze_zero (g:= fun k=> magnify q k*((|x i j|)+d k) / ((side q k).val:ℝ)) (fun _=>by positivity) (fun k=> (div_le_div_of_nonneg_right (ht k) (Nat.cast_nonneg _)) ) -- gcongr
            have h1:= (epsilon_zero hq).mono_right inf_le_left
            have hε:= side_rate hq 1
            convert! (hε.mul (h1.const_add |x i j|)) using 2 <;> [skip;simp]
            dsimp [d,magnify];ring
        filter_upwards [hl.eventually (gt_mem_nhds (show (0:ℝ)<(1/3:ℝ) by norm_num))] with k hk
        try dsimp only [Set.mem_Iio] at hk
        rw [div_lt_div_iff₀ (by positivity) (by norm_num),one_mul] at hk -- maybe
        have hz : |((a k):ℝ)| * 3<((side q k).val:ℝ):=hk
        rw [← Int.cast_abs] at hz
        have hw : |a k| * 3 < ((side q k).val:ℤ):=by exact_mod_cast hz
        have hge:=le_abs_self (a k); have hge₁:=neg_le_abs (a k)
        exact (by omega : -((side q k).val:ℤ)<2*a k∧2*a k≤((side q k).val:ℤ))
   filter_upwards [eventually_all.mpr fun i=>eventually_all.mpr fun j=>he i j] with k hk
   change Extraction.address _ _ = _;funext i;exact Eq.symm (lift_eq_iff.mpr ⟨rfl,hk i⟩)

lemma choose_sample (x:Points n):Tendsto (fun k=>sample q k (signal q k x)) atTop (𝓝 x):=by
    rw [tendsto_iff_dist_tendsto_zero];refine squeeze_zero' (Eventually.of_forall fun k=>dist_nonneg) ((valid hq x).mono fun k hk=> deck_dist q hk) ?_
    simpa only [mul_zero] using! ((epsilon_zero hq).mono_right inf_le_left).const_mul (4*n : ℝ)

lemma sample_position {m:ℕ}(x:Points n)(u : offsets q n m)(i:Fin n) :
      sample q m u i= epsilon q m • Next.Rank.CellsInt.mapZ (Lattice.lift (u i)):=rfl
lemma sample_each {x:Points n}{u:(m:ℕ) → offsets q n m}(h:Tendsto (fun m=>sample q m (u m)) atTop (𝓝 x))(i:Fin n):
    Tendsto (fun m=> epsilon q m • Next.Rank.CellsInt.mapZ (Lattice.lift (u m i))) atTop (𝓝 (x i)):=by
    have hp := ((PiLp.continuous_apply 2 (fun _ : Fin n=> E4) i).tendsto x).comp h
    convert hp using 2;rfl
end YM.PertExtension.LatticePT.Grid
