import YM.Contacts.Mat.Bleed
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Mat
open Function Filter Metric Set
open scoped Topology BigOperators
variable {n:ℕ}{x b:ℝ}{τ: Type*}[Fintype τ]

-- leakage allowed n*card(steam)
def clusterRadius (τ:Type*)[Fintype τ](n:ℕ):ℝ := 2+ ((n+1)*(Fintype.card τ + 1):ℕ)
lemma clusterRadius_pos : 0< clusterRadius τ n := by unfold clusterRadius; positivity
/-- Avoid a fixed number of forbidden *absolute* coordinates, not only the indexed positions. Shift only forwards from current coordinate. -/
lemma between_avoiding (x b:ℝ)(hb:0<b)(t:τ→ℝ): ∃ P:Nodes n (clusterRadius τ n), ∀ i, (∃ j:ℤ, x+P.v i * b=b*j) ∧ ∀ j, x+P.v i * b≠t j:= by
   classical
   let w:= x/b; let k : ℤ:= ⌈w⌉; let T:= Fintype.card τ; let s i:= ((T+1)*i:ℕ); let g (i:ℕ)(j:Fin (T+1)):ℤ:= k+(s i+j.val:ℕ)
   have hh i:Injective (fun j=> b*(g i j:ℝ)):=by
       intro a k he; apply Fin.ext; have hk:=mul_left_cancel₀ hb.ne' he; have h : g i a=g i k:= by exact_mod_cast hk
       unfold g at h; omega
   have h i:∃ j,∀ p,b*(g i j:ℝ) ≠ t p:=by
       by_contra! hl
       choose z hz using hl; have he:Injective z:= fun x y he=> hh i ((hz x).trans ((congr_arg t he).trans (hz y).symm))
       have hp := Fintype.card_le_of_injective _ he; rw [Fintype.card_fin] at hp; dsimp only [T] at *; omega
   choose a ha using h; let m:=fun i:Fin (n+1)=>g i.val (a i.val); let p (i:Fin (n+1)):= (m i:ℝ)-w
   have hy i: x+p i*b=b*(m i:ℝ):=by unfold p w; field_simp; ring
   have ht : StrictMono m:=by
       intro i j he; let u:= (a i.val).val; have hu:= (a i.val).isLt; have hx:T+1>0:= by omega
       have he:s i.val + u < s j.val:= lt_of_lt_of_le (show s i.val + u < s i.val+(T+1) by dsimp [u]; omega) (by
           rw [show s i.val+(T+1)=s (i.val+1) from (by unfold s;ring)]; exact Nat.mul_le_mul_left _ (Fin.lt_def.mp he))
       unfold m g; dsimp [u] at *; omega
   have hP (i): p i∈ Icc 0 (clusterRadius τ n):=by
       have hl:w ≤ k := Int.le_ceil _; have hr:(k:ℝ)< w+1:= Int.ceil_lt_add_one w
       have he : k ≤ m i:= by unfold m g; omega
       have ht:m i ≤ k+(↑((n+1)*(Fintype.card τ + 1):ℕ):ℤ):=by
           have hc:(a i.val).val<T+1:=(a i.val).isLt; have hu : s i.val + (T+1) ≤ (n+1)*(T+1):=by
               rw [show s i.val+(T+1)=(i.val+1)*(T+1) from (by unfold s; ring)]; exact Nat.mul_le_mul_right _ i.isLt
           have ht : s i.val + (a i.val).val ≤ (n+1)*(T+1):= le_trans (Nat.add_le_add_left hc.le _) hu
           exact add_le_add_right (by exact_mod_cast ht) k
       constructor
       · exact sub_nonneg.mpr (hl.trans (by exact_mod_cast he))
       have he:(m i:ℝ) ≤ (k:ℝ)+ (↑((n+1)*(Fintype.card τ + 1):ℕ):ℝ):= by exact_mod_cast ht
       unfold p clusterRadius; linarith
   refine ⟨⟨p,hP,?_⟩,fun i=>⟨⟨m i,hy i⟩,fun j=> by dsimp only; rw [hy i]; exact ha _ _⟩⟩
   intro i j he; have hx j k (h:j<k) : 1 ≤ ‖p j-p k‖:=by
       have hx: (m j:ℝ)+1≤ m k:= by exact_mod_cast (show m j+1≤m k from ht h)
       unfold p; rw [Real.norm_eq_abs,abs_of_nonpos (by linarith)]; linarith
   rcases lt_or_gt_of_ne he with H|H; exact hx i j H; rw [norm_sub_rev]; exact hx j i H
end YM.Contacts.Mat
