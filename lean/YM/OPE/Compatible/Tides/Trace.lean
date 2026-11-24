import YM.OPE.Compatible.Tides.View
/-!
# Native logarithmic coefficient without Fourier cutoff falloff. Cesàro cost per vertex progression
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open Pert.Full (incVec)
open Next.Rank.Radian
open scoped BigOperators Classical ContDiff
variable {U:Gloam}{s:ℝ}{M:ℕ}{K:ℕ→ℕ}{f:Cover→ℝ}{F:E4→ℝ}
def stack (n:Side)(f:Cover→ℝ): Cover→ℝ:=fun x=>cutA 1 (addr n x)*f x
lemma steak (n:Side)(x:Cover)(hp:x∉pod (4*n.val)):stack n f x=0:=by
    rw [stack,gridX,romp (by norm_num),zero_mul]; rw [inv_one]; apply le_of_not_gt; intro he; apply hp; apply in_pod.mpr
    have hv:=bead x _ (dew_pos n).le; rw [dew,sizeR,inv_mul_eq_div] at hv; have hx: ((size x):ℝ)/(n.val:ℝ)<4:= hv.trans_lt (by unfold dew sizeR at he;linarith only [he]); exact_mod_cast ((div_lt_iff₀ (Pert.Full.val_pos n)).1 hx).le
lemma steaks (n:Side): Summable (stack n f):= summable_of_ne_finset_zero (fun a (ha:a∉pod (4*n.val))=> steak _ _ ha)
lemma anise_sum (f:Cover→ℝ)(i:ℕ) :
    anise U.q'⁻¹ (U.M i) f = (∑' p, stack (U.M (i+1)) f p) - ∑' p, stack (U.M i) f p:=by
   rw [← Summable.tsum_sub (steaks _) (steaks _)]; apply tsum_congr; intro b; unfold stack; rw [annA,Pi.sub_apply, sub_mul]; congr 2; unfold cutA; rw [one_smul,gridX,gridX,Pert.Band.to_grid,show dew (U.M (i+1))=U.q'⁻¹*dew (U.M i) from (U.h_succ i).trans (by rw [inv_mul_eq_div]; rfl)]
structure Crown (U:Gloam)(x:ℕ→ℕ):Prop where
   small : ∃ r:ℝ,0<r∧ ∀ᶠ i in atTop, r ≤ U.h i * x i
   big : ∃ C:ℝ,0≤C ∧∀ᶠ i in atTop,U.h i * (x i+1:ℝ) ≤ C
lemma pinc (hn:Crown U K)(hf:Quip 4 f F):
  Sake U 0 (fun i=>(∑' x,stack (U.M i) f x)- ∑ x∈pod (K i), f x):=by
   obtain ⟨r,hr,R⟩:=hn.small; obtain ⟨C,hC,L⟩:= hn.big; obtain ⟨A,hA,H⟩:=straight hf; let p:=min r (4:ℝ)⁻¹; have hp:0<p:=lt_min hr (by norm_num); let D:=2*A/p; have hd:0 ≤ D:=by unfold D; positivity
   let B(i):=4*(U.M i).val+K i; apply coseal (s:=16*D*(4+C)) ?_ (by positivity); filter_upwards [R,L] with i Hi hi; rw [pow_zero,mul_one]; let W:Cover→ℝ:= fun x=>if x∈pod (K i) then f x else 0; let h:=U.h i; let g:=stack (U.M i) f-W
   have hv(x): ‖g x‖ ≤ D*h/(notch x:ℝ)^ (3:ℕ):=by
       rw [show g x=_ from rfl]; let y:= addr (U.M i) x; change ‖cutA 1 y*f x - W x‖ ≤ _; have hn:0<h:=U.h_pos i
       have hz:0<(notch x:ℝ):= Nat.cast_pos.mpr (notch_one x)
       by_cases hk:h * (notch x:ℝ) < p
       · have ht: h*(size x:ℝ)<p:=lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by unfold notch; push_cast; linarith : (size x:ℝ)≤ notch x) hn.le) hk
         have hl:x∈pod (K i):=by rw [in_pod]; apply le_of_lt; exact_mod_cast lt_of_mul_lt_mul_left (a:=h) (lt_of_lt_of_le ht (le_trans (min_le_left ..) Hi)) hn.le
         have he: ‖y‖≤1/2:= le_trans (twice_bead x h hn.le) (by have hx': h * (size x:ℝ) ≤ 4⁻¹:= ht.le.trans (min_le_right ..); linarith only [hx'])
         unfold W; rw [cutA,one_smul,Pert.Band.disk_one he,if_pos hl,one_mul,sub_self,norm_zero]; positivity
       have he: ‖W x‖ ≤ ‖f x‖:=by unfold W; split; rfl; rw [norm_zero]; positivity
       grw [norm_sub_le,norm_mul,cutdown,one_mul,he, H]; unfold D; have hk':=not_lt.mp hk; field_simp; nlinarith only [hk',hA,hp,hz] -- field_simp maybe
   have hh:=U.h_pos i; have hk:=fade_low (f:=g) (Q:=B i) (B:=D*h) (r:=0) (fun x _=> hv x) (by exact mul_nonneg hd hh.le) rfl
   rw [tsum_eq_sum (s:=pod (B i))]; swap; · intro b hb; refine steak (U.M i) b (fun h=> hb (in_pod.mpr ((in_pod.mp h).trans (Nat.le_add_right ..))))
   rw [show (∑ x∈pod (K i),f x)=(∑ x∈pod (B i),W x) from by rw [show (∑ x∈pod (K i),f x)= ∑ x ∈pod (K i),W x from Finset.sum_congr rfl (fun j hj=>by unfold W;rw [if_pos hj])]; exact Finset.sum_subset (fun b hb=>in_pod.mpr ((in_pod.mp hb).trans (Nat.le_add_left ..))) (fun i _ hi=> if_neg hi), ← Finset.sum_sub_distrib]; apply le_trans ((Real.norm_eq_abs _).le.trans ((show |∑ x∈pod (B i), g x| ≤ ∑ x∈pod (B i), ‖g x‖ from Finset.abs_sum_le_sum_abs ..) |>.trans hk)); rw [zero_add,pow_one]; have hx:h * ((B i:ℝ)+1) ≤ 4+C:= by
      have he: h*((U.M i).val:ℝ)=1:=inv_mul_cancel₀ (Pert.Full.val_pos _).ne'; unfold B;push_cast;nlinarith only [he,hi]
   grw [show 16*(D*h)*((B i:ℝ)+1)=16*D*(h*((B i:ℝ)+1)) from by ring,hx]
end YM.OPE.Balsam
