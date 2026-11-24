import YM.Comparison.RG02.Moving.Fold
/-!
# Read after folding

(After averaging and dividing.) Compatible with ordinary log cumulant costs per Taylor rank.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Moving.Shift
open Function Filter Finset MeasureTheory YM.Marker YM.Multi Order Assembly Cumulants
open PertExtension.Series PertExtension.Series.Tested Laplace Path
open YM.Extra.Trajectories (connected connected_quiet pass_connected part_sub)
open scoped Topology BigOperators Classical ContDiff
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {r : ℕ}
local notation "δ" => Grade R r
local notation "M" => Board R r
local notation "ψ" => axis R r
variable {f g : ℝ→Grade R r} (h : Seen f) (hs : ∀ᶠ x in 𝓝 0,Order.Symmetric (f x))

lemma read (L : Finset ℕ) (F : ℕ → Grade R r) (k : ℕ) (s : R.Mode) : detail (∑ i∈L,F i) s k=∑ i∈L, detail (F i) s k := by unfold detail; rw [show observe _ _ _ k= _ from (map_sum (observeL (R:=R) (r:=r) k) _ _), Poly.part_sum]; rfl
lemma observe_eval (F : ℝ→ Grade R r) (s : R.Mode) (n : ℕ) (hn : n≤r) : detail (F 0) s n = (n.factorial:ℂ)⁻¹*(F 0).part (Join.pair s (pick r n)) := by rw [detail,observe,if_pos hn,Poly.part_smul]; rfl
include h
lemma watch (s : R.Mode) (n : ℕ) : ContDiffAt ℝ ω (fun t=>detail (f t) s n) 0 := by
   unfold detail observe; split
   · apply contDiffAt_const.mul (h.smooth (Join.pair s (pick r n)))
   exact contDiffAt_const
lemma measures (s : R.Mode) (k n : ℕ) : detail (sight f k) s n=motion (fun t=>detail (f t) s n) k := by
   unfold detail observe; split
   next h' => simp_rw [Poly.part_smul]; exact (mscale _ (h.smooth (Join.pair s (pick r n)))).symm
   simp

omit h
include hs
lemma turns (n : ℕ) : Order.Symmetric (sight f n) := by
   apply Order.symmetric_test; intro i t u he
   rw [sight_at,sight_at]; apply mgerm; filter_upwards [hs] with x hx; rw [← hx.observe_part i t, ← hx.observe_part i u,he]
lemma fuse_symmetric : Order.Symmetric (fuse R r f) := by rw [fuse_time]; exact Symmetric.sum _ _ fun i _=> (turns hs i).mul ((show Order.Symmetric ψ from ⟨_,Order.series_x ..⟩).pow _)
variable {n k m : ℕ} {s : R.Mode}
include h
lemma cog (he : k ≤ r) : detail (sight f n * ψ ^ m) s k = if m≤k then motion (fun t=>detail (f t) s (k-m)) n else 0 := by
   nth_rw 1 [← series_x,← (recollect (turns hs n)), ← map_pow, ← map_mul]; unfold detail
   rw [observation _ _ _ he,PowerSeries.coeff_mul_X_pow']; split
   next h'=> rw [collect_coeff]; exact measures h _ _ _
   rfl
lemma bore (he : k≤r) : detail (fuse R r f) s k = ∑ i∈range (k+1), motion (fun t=> detail (f t) s (k-i)) i := by
   rw [fuse_time,read]; simp_rw [cog h hs he]; rw [← sum_filter]
   congr 1; ext i; simp only [mem_filter,mem_range]; omega

omit h hs in
lemma mono_price {f : ℝ→ℂ} (h : ContDiffAt ℝ ω f 0) : motion (fun t:ℝ=> (t:ℂ)^k*f t) n= if k≤n then motion f (n-k) else 0 := by
   let v (t:ℝ):= (t:ℂ)^k
   let he : Aspiration v (fun i=>if i=k then (1:ℂ) else 0) := by simpa only [Complex.real_smul,mul_one,Complex.ofReal_pow] using! Aspiration.single (1:ℂ) k
   have hx := (ordinary (f:=v*f) (((Complex.ofRealCLM.contDiff.contDiffAt.pow _).mul h).of_le le_top)).unique (he.prod (ordinary (h.of_le le_top)))
   change motion (v*f) n=_; rw [hx]; unfold Tested.conv term
   rw [show PowerSeries.mk (fun i=>if i=k then (1:ℂ) else 0)=PowerSeries.X^k by ext1 i; simp only [PowerSeries.coeff_X_pow,PowerSeries.coeff_mk],mul_comm,PowerSeries.coeff_mul_X_pow']; split <;> simp only [PowerSeries.coeff_mk]
lemma valued (he : k≤r) : motion (fun t:ℝ=> (value (t:ℂ) (f t)).part s) k = detail (fuse R r f) s k:= by
   rw [bore h hs he]; simp_rw [vpart]
   let q (i : ℕ) (t:ℝ) := detail (f t) s i
   have hk : (range (r+1)).filter (fun i=>i≤k)=range (k+1):= by ext i; simp only [mem_filter,mem_range]; omega
   change motion (fun t:ℝ=> ∑ i∈ range (r+1), (t:ℂ)^i*q i t) k=_
   rw [msum (f:=fun i (t:ℝ)=> (t:ℂ)^i*q i t)]; swap; · exact fun i _=> (Complex.ofRealCLM.contDiff.contDiffAt.pow _).mul (watch h s i)
   simp_rw [show ∀ i,motion (fun t:ℝ=> (t:ℂ)^i*q i t) k= if i≤k then motion (q i) (k-i) else 0 from fun i=> mono_price (f:=q i) (watch h s i)] -- unification q
   rw [← sum_filter,hk]
   rw [← Finset.sum_range_reflect]; apply sum_congr rfl; intro i hi
   simp only [Nat.add_sub_cancel]; have hx:= mem_range_succ_iff.mp hi; -- edit
   rw [Nat.sub_sub_self hx]
end YM.Comparison.RG02.Moving.Shift
