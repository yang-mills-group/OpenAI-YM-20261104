import YM.X.Rank.Screen
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
/-!
Compact moment testing in snapshot exponential Gram coordinates. Approximation
used against weighted measures only after the weighted measure bounds.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank.Screen
open Function Set Filter MeasureTheory Matrix
open YM.Next.SectorChange.Gaussian YM.Next.Rank.Normal MvPolynomial Heat
open scoped Topology BigOperators Classical Kronecker NNReal
variable {I A:Type}

abbrev PTS (A:Type) := (A→ℝ)
private def translator (A:Type) := (aeval (fun a:A=> (⟨fun x:PTS A=>x a,continuous_apply a⟩ : ContinuousMap _ _)) : MvPolynomial A ℝ →ₐ[ℝ] _)
lemma translated (p:MvPolynomial A ℝ)(x:PTS A) : translator A p x = aeval x p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [translator]
  | add p q h t => simp only [_root_.map_add, ContinuousMap.add_apply,h,t]
  | mul_X p i h => simp only [_root_.map_mul,ContinuousMap.mul_apply,h]; simp [translator]
lemma polish (K:Set (PTS A))(f:PTS A→ℝ)(hf:Continuous f)(hk:IsCompact K)(ε:ℝ)(hε:0<ε) : ∃ p:MvPolynomial A ℝ,∀ x∈K, ‖aeval x p-f x‖≤ε:=by
  let A₀ := (translator A).range
  have he : A₀.SeparatesPoints := by
    intro x y he; obtain ⟨i,hi⟩:= not_forall.mp (fun h=>he (funext h)); let f:=translator A (X i); exact ⟨_,⟨f,⟨_,rfl⟩,rfl⟩,by change f x ≠ f y; simpa only [f,translated,aeval_X] using hi⟩ -- edit
  obtain ⟨p,⟨q,rfl⟩,H⟩:= ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints he ⟨f,hf⟩ hk hε
  exact ⟨q,fun x hx=>by rw [← translated]; exact (H x hx).le⟩
lemma near_zero {E:Type*} [NormedAddCommGroup E]{x:E}{M:ℝ}(h:∀ ε>0, ‖x‖≤ ε*M):x=0:= by
  apply norm_le_zero_iff.mp; refine ge_of_tendsto (x:=nhdsWithin (0:ℝ) (Ioi 0)) (f:=fun t=>t*M) (by simpa using! (tendsto_id (x:=nhds (0:ℝ)) |>.mono_left (nhdsWithin_le_nhds (s:=Ioi 0))).mul_const M) (by filter_upwards [self_mem_nhdsWithin] with i hi; exact h i hi)
lemma tamePay {Y E:Type*}[MeasurableSpace Y][NormedAddCommGroup E][NormedSpace ℝ E]{μ: Measure Y}{f:Y→E}(h:Integrable f μ){g:Y→ℝ}(hg:Integrable g μ)
    (ht:∀ ε>0, ∃ u:Y→E,Integrable u μ ∧ (∫ x,u x ∂μ)=0 ∧ ∀ y,‖f y-u y‖≤ ε*g y):∫ x,f x ∂μ=0:= by
  refine near_zero (M:=∫ x,g x ∂μ) fun ε hε=> ?_; obtain ⟨u,hu,h0,h'⟩:=ht ε hε
  have H:= norm_integral_le_of_norm_le (f:=fun x=>f x-u x) (hg.const_mul ε) (Eventually.of_forall h')
  rwa [integral_const_mul, integral_sub h hu,h0,sub_zero] at H
variable [DecidableEq I][Fintype I]
section aux
variable {F : Tile I→ℂ}(h:Mirrors F)(v : A→PTS I) [Fintype A]
def snapshots (x:Tile I):PTS A:=fun i=> stamp (v i) x
omit [DecidableEq I] in
lemma snap_bounds (x:Tile I): ‖snapshots v x‖≤1:= by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=> ?_
  exact (Real.norm_of_nonneg (stamp_range _ x|>.1.le)).le.trans ((stamp_range (v i) x).2)
omit [DecidableEq I] in
@[fun_prop] lemma snaps : Continuous (snapshots v) := continuous_pi fun i=> stamp_cont (v i)
include h
lemma spark (p:MvPolynomial A ℝ) : Mirrors (fun x:Tile I=> aeval (snapshots v x) p • F x):=by
  induction p using MvPolynomial.induction_on with
  | C a=> simp_rw [aeval_C]; exact h.scales (a:ℂ) -- real coe
  | add p q hp hq=> simp_rw [map_add,add_smul]; exact hp.plus hq
  | mul_X p i hp=> simp_rw [mul_comm p,map_mul,aeval_X,mul_smul]; exact hp.stamp_test (v i)

lemma continuousPay {g:PTS A→ℝ}(hg:Continuous g): Mirrors (fun x:Tile I=> g (snapshots v x) • F x):= by
  intro P hp; let K:=Metric.closedBall (0:PTS A) 1; have hK:IsCompact K:= isCompact_closedBall ..
  obtain ⟨M,hM⟩:= hK.exists_bound_of_continuousOn hg.continuousOn
  have he(x:Tile I): snapshots v x∈ K:= mem_closedBall_zero_iff.mpr (snap_bounds v x)
  obtain ⟨hP,hp'⟩:= h P hp; have hi:= hP.bdd_smul M (hg.comp (snaps v)).aestronglyMeasurable (Eventually.of_forall (p:=fun (x:Tile I)=> ‖(g ∘ snapshots v) x‖ ≤ M) (fun x=> hM _ (he x)))
  refine ⟨hi,tamePay hi hP.norm ?_⟩
  intro ε hε; obtain ⟨p,hp'⟩:= polish K g hg hK ε hε; obtain ⟨hq,H⟩:= spark h v p P hp
  refine ⟨_,hq,H, fun x=> ?_⟩; rw [← sub_smul,norm_smul, norm_sub_rev]; apply mul_le_mul_of_nonneg_right (hp' _ (he x)) (norm_nonneg _)
end aux
end YM.PositionX.Rank.Screen
