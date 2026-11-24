import YM.MS.Shine.Purity
import YM.MS.Shine.Classic
/-!
# pure Pole-only on bare terms. no value∞ or smearing.

Plain (not just germ-equivalent). Negative powers incl value=0 at zero (zpow convention).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Shine
open Set Filter Function Finset MeasureTheory Metric Arc
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open scoped Topology ContDiff
variable {I:Type}{G:Gauge}{F H:Mob G}{f g:ℂ→ Mob G}{m n j:ℕ}
def cone (G:Gauge): Submodule ℂ (ℂ→Mob G):= Submodule.span ℂ { f| ∃ m:ℕ,0<m ∧∃ F:Mob G,f=Ice m F}
abbrev Cool (f:ℂ→ Mob G): Prop:= f∈cone G
lemma iceC (F:Mob G)(n:ℕ)(h:0<n): Cool (Ice n F):= Submodule.subset_span (show Ice n F ∈ _ from (show ∃ m:ℕ,0<m ∧∃ H:Mob G,Ice n F=Ice m H from ⟨n,h,F,rfl⟩)) -- underscore
lemma iceScale (h:F=0): Ice n F= 0:= by rw [h]; ext; simp [Ice]
lemma pack (h:m≤n)(F:Mob G): paid n (Ice m F)=ᶠ[dotty] paid (n-m) (fun _=> F):= by
   filter_upwards [dotty_non] with i hi; unfold paid Ice; nth_rw 1 [show n=n-m+m by omega]; rw [pow_add,mul_smul,inv_pow, smul_inv_smul₀ (pow_ne_zero m hi)]
lemma lamp (h: kPrice F)(he:m≤n): altitude n (Ice m F):= Live.congr (pay_live _ (Live.stays h)) ( pack he F|>.symm)
lemma icePick (h:kPrice F)(ht:m≤n): Pick j (paid n (Ice m F)) (if j=n-m then F else 0):= ( hump j (n-m) F h).congr (pack ht F).symm
private def cany (n:ℕ)(F:ℂ→Mob G): Prop:=∃ X:ℕ→Mob G,F=∑ i∈Finset.range n,Ice (i+1) (X i)
private lemma canz (h:m≤n)(he:cany m f): cany n f:= by
    induction n,h using Nat.le_induction with
    | base=> exact he
    | succ n h ih=>
       obtain ⟨X,H⟩:= ih; let Y i :=if i=n then (0:Mob G) else X i; refine ⟨Y,?_ ⟩; rw [Finset.sum_range_succ,iceScale (show Y n=0 by simp [Y]),add_zero,H]; apply Finset.sum_congr rfl; intro i hi; rw [show Y i=X i from if_neg (Finset.mem_range.mp hi).ne]
private lemma can0 (n:ℕ): cany n (0:ℂ→Mob G):= ⟨ _,Eq.symm (Finset.sum_eq_zero (f:=fun i:ℕ=>Ice (i+1) (0:Mob G)) fun _ _=> iceScale rfl)⟩ -- name n underscore
lemma polar (h:Cool f): ∃ n:ℕ,∃ X:ℕ→ Mob G,f=∑ i∈Finset.range n,Ice (i+1) (X i):= by
   change ∃ n:ℕ,cany n f; refine Submodule.span_induction (p:=fun f _=>∃ n:ℕ,cany n f) ?_ ⟨0, can0 0⟩ ?_ ?_ h
   · rintro f ⟨_|i,hp,F,rfl⟩; omega; let X k := if k=i then F else 0; refine ⟨i+1,X,?_⟩; rw [Finset.sum_eq_single i]; --- inspect h? used below
     all_goals first| (intro k hk ht; exact iceScale (if_neg ht)) | simp [X]
   · intro x y h h' hp hq; obtain ⟨m,hp⟩:=hp; obtain ⟨n,hq⟩:=hq; obtain ⟨X,H⟩:=canz ( le_max_left m n) hp; obtain ⟨Y,J⟩:=canz (le_max_right m n) hq; refine ⟨max m n,X+Y,?_⟩; rw [H,J, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i hi; ext; simp [Ice, mul_add] -- ext stack
   intro c f h H; obtain ⟨n,X,H⟩:=H; refine ⟨n,c • X,?_⟩; rw [H,Finset.smul_sum]; apply Finset.sum_congr rfl; intro i hi; ext; simp only [Ice,Pi.smul_apply,smul_eq_mul]; ring
lemma paid_zero_tends (hf:Wind f dotty F)(ht:0<n): Wind (paid n f) dotty 0:= by
    intro m l; convert Tendsto.smul ((Tendsto.mono_left (tendsto_id (x:=𝓝 (0:ℂ))) nhdsWithin_le_nhds).pow n) (hf m l) using 1; rfl
    simp [zero_pow ht.ne']
private lemma towards (x:ℕ→Mob G): Wind (paid (n+1) (∑ i∈Finset.range (n+1), Ice (i+1) (x i))) dotty (x n):= by
    let U i:=Ice (i+1) (x i); let g i:= paid (n+1) (U i); intro m l; have he (i:ℕ)(hi:i<n): Tendsto (fun z=>g i z m l) dotty (𝓝 0):= by
        have hp:= (paid_zero_tends (f:=fun _:ℂ=>x i) (fun _ _ => tendsto_const_nhds) (show 0<n+1-(i+1) by omega)).congr (pack (m:=i+1) (n:=n+1) (by omega) (x i)|>.symm); exact hp m l
    have hm : Wind (g n) dotty (x n) := by obtain hv:= pack (le_refl (n+1)) (x n); rw [Nat.sub_self,pay_zero] at hv; exact Wind.congr (F:=x n) (fun _ _=> tendsto_const_nhds) hv.symm
    have hu(q:ℂ): paid (n+1) (∑ i∈Finset.range (n+1),U i) q m l= (∑ i∈ Finset.range n, g i q m l)+g n q m l:= by unfold paid g; simp only [Finset.sum_range_succ,Pi.add_apply,Finset.sum_apply,smul_add,Finset.smul_sum, Pi.smul_apply]; rfl
    change Tendsto (fun q=> paid (n+1) (∑ i∈Finset.range (n+1),U i) q m l) _ _; simp_rw [hu]; convert (tendsto_finsetSum (Finset.range n) (fun i hi=>he i (Finset.mem_range.mp hi))).add (hm m l) using 1; simp
lemma deep_zero (h:Cool f)(he:Wind f dotty F): f=0:= by
    obtain ⟨n,x,hp⟩:= polar h; clear h; induction n generalizing x with
    | zero=> simpa using hp
    | succ n ih=>
       have hm : x n=0:= by apply Wind.unique (towards x); rw [← hp]; exact paid_zero_tends he (by omega)
       exact ih x (by rw [Finset.sum_range_succ, iceScale hm,add_zero] at hp; exact hp)
end YM.MS.Shine
