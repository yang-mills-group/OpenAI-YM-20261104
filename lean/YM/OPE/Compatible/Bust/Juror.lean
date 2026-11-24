import YM.OPE.Compatible.Bust.Proton
/-!
# Operator calculus. Strong OpTopology
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Float
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08
open scoped Topology BigOperators Classical
variable {I K E F X:Type}{m r i j n k:ℕ}{C D:ℝ}
section
variable [NormedAddCommGroup E][NormedAddCommGroup F][NormedSpace ℝ E][NormedSpace ℝ F]
structure Robust (f: Filter X)(p:X→ E→L[ℝ] F)(q:E→L[ℝ] F):Prop where
    p1 :∃ a:ℝ, 0≤a ∧ ∀ᶠ v in f, ‖p v‖ ≤ a
    p2 : ∀ e:E,Tendsto (fun i=> p i e) f (𝓝 (q e))
lemma qualifies (p:X→ E→L[ℝ] F)(q:E→L[ℝ] F) {f:Filter X}(h:Robust f p q) (v:X→E)(x:E) (hp:Tendsto v f (𝓝 x)): Tendsto (fun i=> p i (v i)) f (𝓝 (q x)) :=by
     obtain ⟨a,ha,H⟩:= h.p1; have he : Tendsto (fun i=> p i (v i-x)) f (𝓝 0):=by
          apply tendsto_zero_iff_norm_tendsto_zero.mpr; have hh:Tendsto (fun i=> a*‖v i-x‖) f (𝓝 0):=by simpa only [sub_self,norm_zero,mul_zero] using! ((hp.sub_const x).norm.const_mul a)
          exact squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) (H.mono fun i ht=> ((p i).le_opNorm _).trans (by gcongr)) hh
     rw [show 𝓝 (q x)=𝓝 (0+q x) from by rw [zero_add]]; apply (he.add (h.p2 x)).congr;intro i; rw [map_sub]; simp
lemma robust_single {p:X→E →L[ℝ] E}{q:E→L[ℝ] E}{f:Filter X}{g:X→E}{v:E}(h:Robust f p q)(hp:Tendsto g f (𝓝 v)) (i:ℕ): Tendsto (fun t=>(p t).toLinearMap^i |> fun s=>s (g t)) f (𝓝 ((q.toLinearMap^i) v)):=by
     induction i with
     | zero=> exact hp
     | succ i ih=>
          change Tendsto (fun t=>((p t).toLinearMap^ (i+1)) (g t)) f (𝓝 ((q.toLinearMap^ (i+1)) v))
          simp_rw [pow_succ',End.mul_apply]; exact qualifies p q h _ _ ih
lemma fixStrong {p:X→E →L[ℝ] E}{q:E→L[ℝ] E}{f:Filter X}(h:Robust f p q)(v:ℝ)(i:ℕ){g:X→E}{e:E}(hp:Tendsto g f (𝓝 e)): Tendsto (fun t=>fixExp (p t).toLinearMap v i (g t)) f (𝓝 (fixExp q.toLinearMap v i e)):=by simp_rw [Hflow]; apply tendsto_finsetSum _; exact fun j _=>tendsto_const_nhds.smul (robust_single h hp j)
end
noncomputable def vibeC (I:Type)(m r:ℕ)(p:RowB I):stave m (r+2) I→L[ℝ] stave m (r+2) I:=(dentF p m r).choose
lemma vibe_n (p:RowB I): ‖vibeC I m r p‖ ≤ p.fare:= (dentF p m r).choose_spec.2
lemma vibe_eq (p:RowB I)(x:stave m (r+2) I): vibeC I m r p x= dent (m:=m) p x:= congr_fun (dentF p m r).choose_spec.1 x
variable {p:K→RowB I}{x:RowB I}{f:Filter K}
structure Dull (f:Filter K)(p:K→ RowB I)(x:RowB I): Prop where
     born : ∃ A:ℝ,0≤A ∧ ∀ᶠ i in f,(p i).fare≤A
     limit (u v:I) (δ:Cover) : Tendsto (fun i=>(p i).val u v δ) f (𝓝 (x.val u v δ))
lemma vibing (h:Dull f p x): Robust f (fun i=> vibeC I m r (p i)) (vibeC I m r x) := by
     obtain ⟨A,ha,hp⟩:= h.born; refine ⟨⟨A,ha,hp.mono fun _ hi=>vibe_n _|>.trans hi⟩,fun v=> ?_⟩; simp_rw [vibe_eq]; apply tendsto_sub_nhds_zero_iff.mp; apply tendsto_zero_iff_norm_tendsto_zero.mpr
     let V(k):= dent (m:=m) (p k) v-dent (m:=m) x v; let W:=seed m (r+2) I v; let y(k)(i):=figure m i*‖seed _ _ _ (V k) i‖; have he(k):‖V k‖=∑' i:Page I (r+2), y k i:= (sprig _ _ (V k)).tsum_eq.symm
     change Tendsto (fun k=>‖V k‖) f _; simp_rw [he]; rw [show 𝓝 (0:ℝ)=𝓝 (∑' _:Page I (r+2),(0:ℝ)) from by simp]; let a:= A+x.fare; let T i:= figure m i*‖W i‖
     have hd(k i):y k i=T i * ‖throat (p k) i - throat x i‖ := by unfold y V; rw [map_sub,nailD,nailD, Pi.sub_apply]; change figure m i*‖W i*_ - W i*_‖= _;rw [← mul_sub,norm_mul]; unfold T; rw [mul_assoc]
     have hs(i):Tendsto (fun k=> throat (p k) i) f (𝓝 (throat x (r:=r) i)):=h.limit ..
     simp_rw [hd]; refine tendsto_tsum_of_dominated_convergence ((show Summable T from (humor v).2.1).mul_right a) (fun i=> ?_) ?_
     · simpa only [sub_self,norm_zero,mul_zero] using! (((hs i).sub_const (throat x i)).norm.const_mul (T i)) -- _
     filter_upwards [hp] with k hk i; -- wrong
     have ht(i):0 ≤ T i:=(humor v).1 i
     rw [Real.norm_of_nonneg (mul_nonneg (ht _) (norm_nonneg _))]; exact mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add ((p k).lease ..|>.trans hk) (x.lease ..))) (ht _)
end YM.OPE.Silt.Float
