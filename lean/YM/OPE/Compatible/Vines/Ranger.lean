import YM.OPE.Compatible.Vines.Shed
/-!
# Field reading from grade-preserving substitution
Uses one moment slack for cutting off gauge functions. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Labels Tensor ContinuousMultilinearMap WithLp
open scoped Topology BigOperators Classical
variable {r d m n:ℕ}{c:ℝ}{T I:Type*}{G:Gauge}
namespace Script
open Page
lemma quiet_up {x:fieldX T} (h:Quiet x d) (hp:d≤n): Quiet x n:=by
   obtain ⟨C,hc,H⟩:=h; exact ⟨C,hc,fun i=>(H _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (show 1 ≤ (notch i.1:ℝ) by exact_mod_cast notch_one _) hp) hc)⟩
lemma cliff_cost {T: Ridge G d}: Quiet (mountain (driftX T)) (d+1):=by
   obtain ⟨C,hc,H⟩:=low_quiet (letterL (rosary T))
   refine ⟨C*2^(d+1)+C,by positivity,fun p=>?_⟩; unfold mountain; rw [add_mul,mul_assoc]; apply (norm_sub_le ..).trans; apply add_le_add _ (H _); exact (H (p.1+Lattice.step p.2.1,p.2.2)).trans (mul_le_mul_of_nonneg_left (ascentStep ..) hc)
lemma warp_cost (T:Ridge G d): Low (debtX T) (d-1):=fun i=>by obtain ⟨x,hx,-,hg⟩:=ridgeL T i;exact ⟨_,hx,hg⟩
lemma swapK {A:Type*}{B:Type*}[DecidableEq A] (i:A)(p:B)(x:A→B)(v:A→ℕ) {k:ℕ}(F:B→ℕ→Prop)(hg:∀ j,j≠i→ F (x j) (v j))(h:F p k):∀ j,F ((update x i p) j) (update v i k j):=fun j=>by by_cases H:j=i<;>simp [H,h,hg]
lemma sum_v {i:Fin r} (y:Fin r→ℕ)(w:ℕ): ∑ j,(update y i w) j= w+∑ j∈univ.erase i, y j:=by
   rw [← add_sum_erase univ (update y i w) (mem_univ i),Function.update_self]; exact congr_arg (w+·) (sum_congr rfl (fun _ he=>update_of_ne (ne_of_mem_erase he) ..))
variable {u v:Fin r→fieldX (Shade G)}{p:Script (Shade G) r}{k:Fin r→ℕ}
lemma veil (hp:soot m p c)(h:Bells p n) (H:p.abides) (i:Fin r) (x: Fin r→fieldX (Shade G)) (T:Ridge G d) (he:k i=d) (hy:∀ j,j≠i→Low (x j) (k j)) (hr:(∑ j,k j)=n)(hx:n<m): wholeX p (update x i (ledge T))=wholeX p (update x i (ledge (warp T))):=by
   let g:=update k i (d+1); have hv:= add_sum_erase univ k (mem_univ i); rw [he,hr] at hv; have hf:(∑ j,g j)≤m:=by unfold g; rw [sum_v]; omega
   let w:= driftX T; have hP:wholeX p (update x i (mountain w))=0:= crest_zero _ H hp x i w g hf (fun j hi=>by rw [show g j=k j from update_of_ne hi ..]; exact low_quiet (hy j hi)) (show Quiet w (g i) from by rw [show g i=d+1 from update_self ..]; exact low_quiet (letterL _))
   let q(j:fieldX (Shade G)):= update x i j; by_cases ht:d=0
   · clear he; subst d; rw [ridge_base]; rw [show ledge (warp T)=(0:fieldX _) from funext fun i=>by change diagonal (warp T i.2.1) _ i.2.2=_; rw [warp_base]; rfl, hP]; unfold wholeX; simp_rw [show ∀ a:Page _ _,wordX (update x i 0) a=0 from fun a=> prod_eq_zero (mem_univ i) (by change q 0 i _=0; unfold q;rw [Function.update_self];rfl)]
     simp
   let e:= debtX T; let u:= ledge (warp T); have hE:Quiet e (d+1):=quiet_up (low_quiet (warp_cost _)) (by omega); have hU:Quiet u (d+1):= quiet_up (low_quiet (ledgeL _)) (by omega); have hg(v w:fieldX (Shade G))(hv:Quiet v (d+1))(hw:Quiet w (d+1)): wholeX p (q (v+w))=wholeX p (q v)+wholeX p (q w):=
       choir i hp (swapK i v _ k Quiet (fun j hi=> low_quiet (hy j hi)) hv) (swapK i w _ k Quiet (fun j hi=>low_quiet (hy j hi)) hw) hf (by simp [q]) (fun j hj=>by simp [hj,q])
   have hu : wholeX p (q e)=0:=by
       let dH:= update k i (d-1); have hj : (∑ j,dH j)< n:=by unfold dH; rw [sum_v]; omega
       exact hail hp (swapK i e _ k Low hy (warp_cost T)) (hj.le.trans hx.le) hj h
   change wholeX p (q _) = wholeX p (q _); rw [show ledge T=e+u+mountain w by change ledge T= (ledge T -mountain w -u) +u +mountain w; abel] -- reverse
   rw [hg _ _ (quietAdd hE hU) cliff_cost,hP,hg _ _ hE hU, hu,zero_add,add_zero]
lemma winds (h:soot m p c)(hP:Bells p n)(hp:p.abides) (x:∀ i:Fin r,Ridge G (k i)) (he:∑ i,k i=n)(hx:n<m): wholeX p (fun i=>ledge (x i))= wholeX p (fun i=>ledge (warp (x i))):=by
   let v:Fin r→fieldX (Shade G):=fun i=> ledge (x i); let y:= fun i=>ledge (warp (x i)); have ht (s:Finset (Fin r)): wholeX p v=wholeX p (fun i=>if i∈s then y i else v i):=by
       induction s using Finset.induction_on with
       | empty=>simp
       | insert i s hi ih=>
          let z(j:Fin r):= if j∈s then y j else v j; let Y:=x i; have hz:z i=v i:=if_neg hi; have hs:= veil h hP hp i z Y rfl (fun j _=>by unfold z;split; exact ledgeL _; exact ledgeL _) he hx; rw [ih]
          rw [show update z i (ledge Y)=z by rw [← (show z i=ledge Y from hz)]; simp] at hs
          rw [show (fun j=> if j∈insert i s then y j else v j)=update z i (ledge (warp Y)) from funext fun j=>by by_cases he:j=i<;>simp [z,he,y,Y]]; exact hs
   have H:=ht Finset.univ; simpa only [Finset.mem_univ,if_true] using H
end Script
end YM.OPE.Flume
