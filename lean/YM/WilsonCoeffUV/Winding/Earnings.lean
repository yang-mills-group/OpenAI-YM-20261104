import YM.WilsonCoeffUV.Marked.Paths.Barrier
/-!
# Winding earnings across a formal Q-LOCAL step.

All n pointwise inside 4d<n (d true terrain taxicab): no alias
within *arrays* there. This is a LOCAL operation; its winding rate may be
purchased post block, and is NOT used to fund the preblock repeated strips
for the UV bulk estimates.
-/
set_option autoImplicit false
set_option maxHeartbeats 430000
noncomputable section
namespace YM.WilsonCoeffUV.Winding
open Function Filter Lattice RG Embroider Soil Bank Laurent Metric Gauge Power Matrix Precision Wilson Tree Exterior Blue Work.F08 FreeResolvent
open scoped Topology BigOperators
variable {n L:Side}{ι U X α β V:Type*}{i j k r:ℕ}{s a A B t q :ℝ}
lemma nearTau {x y:Cover}(h:2*Bank.terrain.gap x y < n.val): lift (wrap n y-wrap n x)=y-x:=by rw [← map_sub]; exact size_centers n _ le_rfl (Nat.succ_le_iff.mpr h)
lemma exactGap {x y:Cover}(h:4*Bank.terrain.gap x y<n.val): Bank.terrain.gap x y=(tor n).gap (wrap n x) (wrap n y) := by unfold tor; simp only; rw [nearTau (by omega)]; rfl
lemma league_cash (d:Bank.Distance U)[Fintype ι]{x:ι→U}{a:U}{D:ℕ}(h:∀ i, d.gap a (x i)≤D): league d x≤2*D:=by
    refine league_le d _ fun i j=> (d.tri (x i) a (x j)).trans ?_
    rw [d.swap _ a, two_mul]; exact Nat.add_le_add (h i) (h j)
lemma exact_course [Fintype ι]{x:ι→Cover}(h:4*league Bank.terrain x<n.val) : league (tor n) (wrap n ∘ x)=league Bank.terrain x:=by
    have he i j:(tor n).gap ((wrap n ∘ x) i) ((wrap n ∘ x) j)=Bank.terrain.gap (x i) (x j):= Eq.symm (exactGap (by have he:=leg_le Bank.terrain x i j; omega))
    unfold league; simp_rw [he]
lemma unfoldReady {p:Cover}{y:dock Cover α k}(h:∀ i,4*Bank.terrain.gap p (y i).1<n.val): unfoldAt p (slideC n y)=y:=by
    ext1 i; refine Prod.ext ?_ rfl; change p+lift (wrap n (y i).1-wrap n p)=_; rw [nearTau (by specialize h i; omega)]; abel

def catchW (s:ℝ)(i:ℕ): ℝ:= Real.exp (-s*i)
lemma catch_hot (s:ℝ)(i:ℕ): 0≤catchW s i:= (Real.exp_pos _).le
lemma catch_width (h:t≤s)(i:ℕ):catchW s i ≤ catchW t i:= Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg h) (by positivity))
lemma catch_peak (h:0≤s)(i): catchW s i ≤ 1:= by refine le_trans (catch_width h i) (le_of_eq ?_); simp [catchW]

variable [NormedAddCommGroup V]
structure Wound (P: U→V) (F:X→ V) (n:Side) (fold:X→U)(d:X→ℕ)(s A:ℝ):Prop where
   coal :0≤A
   local_w (x:X): 4*d x<n.val→ ‖P (fold x)-F x‖ ≤ A * catchW s n
variable {P Q:U→V}{F Z:X→V}{f:X→U}{d:X→ℕ}
lemma Wound.mono (h:Wound P F n f d s A)(p:t≤s): Wound P F n f d t A:=⟨h.coal,fun x v=>(h.local_w x v).trans (mul_le_mul_of_nonneg_left (catch_width p n) h.coal)⟩
lemma Wound.more (h:Wound P F n f d s A)(p:A≤B): Wound P F n f d s B:=⟨h.coal.trans p,fun x v=>(h.local_w x v).trans (mul_le_mul_of_nonneg_right p (catch_hot ..))⟩
lemma wound_add {x y w z:V}(p:‖x-y‖≤A*q)(h:‖w-z‖≤B*q): ‖x+w-(y+z)‖ ≤ (A+B)*q:=by rw [show x+w-(y+z)=(x-y)+(w-z) from by abel]; exact (norm_add_le ..).trans ((add_le_add p h).trans_eq (add_mul ..).symm)
lemma Wound.add (h:Wound P F n f d s A)(p:Wound Q Z n f d s B): Wound (P+Q) (F+Z) n f d s (A+B):=⟨add_nonneg h.coal p.coal,fun x v=>wound_add (h.local_w x v) (p.local_w x v)⟩
lemma Wound.μ [NormedSpace ℝ V] (h:Wound P F n f d s A)(a:ℝ): Wound (a•P) (a•F) n f d s (‖a‖*A):=by
   refine ⟨mul_nonneg (norm_nonneg _) h.coal,fun x v=> ?_⟩; simp only [Pi.smul_apply, ← smul_sub,norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left (h.local_w x v) (norm_nonneg _)
lemma Wound.zero: Wound (0:U→V) 0 n f d s 0:=⟨le_rfl,by simp⟩

lemma Wound.sum {P:ι→U→V}{F:ι→X→V}{C:ι→ℝ}(S:Finset ι)(h:∀ i∈ S,Wound (P i) (F i) n f d s (C i)): Wound (∑ i∈ S,P i) (∑ i∈ S,F i) n f d s (∑ i∈ S,C i):=by
   classical
   induction S using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact Wound.zero
   | @insert i S hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi,Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).add (ih (fun j hj=> h j (Finset.mem_insert_of_mem hj)))
lemma spent_ceil {u d:ℕ}(h:¬4*d<u)(p:0≤s): catchW (s/2) d≤catchW (s/32) u * catchW (s/4) d:=by
    have hp:u ≤ 4*d:=by omega
    have hx:(u:ℝ) ≤ 4*d:=by exact_mod_cast hp
    unfold catchW; rw [← Real.exp_add,Real.exp_le_exp]; linarith [mul_le_mul_of_nonneg_left hx p,mul_nonneg p (show 0 ≤ (d:ℝ) from by positivity)]
lemma spent_floor {u d:ℕ}(h:4*d<u)(p:0≤s):catchW s u ≤ catchW (s/32) u *catchW (s/4) d:=by
    have hp:d≤u:=by omega
    have hx:(d:ℝ)≤u:=by exact_mod_cast hp
    unfold catchW; rw [← Real.exp_add,Real.exp_le_exp]; linarith [mul_le_mul_of_nonneg_left hx p, mul_nonneg p (show 0 ≤ (u:ℝ) from by positivity)]

def tailC (i:ℕ)(s:ℝ): ℝ:= if i=0 then 1 else s/i
lemma tail_good (i:ℕ)(h:0<s):0<tailC i s:=by unfold tailC; split; exact one_pos; rename_i hz; exact div_pos h (by exact_mod_cast Nat.zero_lt_of_ne_zero hz)
lemma sail_floor {z:dock Cover α k}{p:Cover}{d:ℕ}(h:∀ i,Bank.terrain.gap p (z i).1≤d)(hs:0<s): catchW s d ≤ sail (tailC k s) Bank.terrain p z:=by
    by_cases hp:k=0
    · subst k; unfold sail; simp only [Finset.univ_eq_empty,Finset.prod_empty]; exact catch_peak hs.le d
    have ht:= sail_cut (v:=0) (Nat.zero_le d) le_rfl hs (Nat.zero_lt_of_ne_zero hp) p z h
    rw [tailC,if_neg hp]; simpa only [catchW,sub_zero,Nat.cast_zero,mul_zero,Real.exp_zero,one_mul,neg_zero] using ht
variable [CompleteSpace V] [Fintype α]
open Classical in
/-- Integrator of pointwise one-torus discounts. `h` only asked on
unfolded jobs (so it can require anchoring/near-center gains for jobs with a site tied). -/
lemma broker (p:Cover)(F:dock Cover α k→ V)(T:dock (Site n) α k→ V)(d:dock Cover α k→ℕ)(he:0<s)(hg:0≤A) (ht:Summable F)
    (u:let W:=fun y=> (if unfoldAt p (slideC n y)=y then T (slideC n y) else 0);∀ y,W y-F y≠0 →
       (∀ i,Bank.terrain.gap p (y i).1≤ d y)∧ (4*d y<n.val→ ‖W y-F y‖≤ A*catchW s n) ∧ (‖W y-F y‖≤ (A+A)*catchW (s/2) (d y))) :
    ‖(∑ i,T i)-∑' i,F i‖ ≤ ((A+A)*(boardPay α (tailC k (s/4)))^k)* catchW (s/32) n :=by
   classical
   let W:=fun y=> (if unfoldAt p (slideC n y)=y then T (slideC n y) else 0)
   let q:= (A+A)*catchW (s/32) n; let v:= tailC k (s/4); let D:= W-F
   have hp:0≤ q:=mul_nonneg (add_nonneg hg hg) (catch_hot ..)
   have hv:0<v:= tail_good _ (by positivity)
   have hh y: ‖D y‖ ≤ q*sail v Bank.terrain p y:=by
       by_cases hz : D y=0
       · rw [hz,norm_zero]; exact mul_nonneg hp (sail_nn ..)
       let z:= d y; obtain ⟨H,g,h⟩:= u y hz; apply le_trans _ (mul_le_mul_of_nonneg_left (sail_floor H (show 0<s/4 from by positivity)) hp); unfold q; rw [mul_assoc]; by_cases w:4*z<n.val
       · exact (g w).trans (mul_le_mul (le_add_of_nonneg_right hg) (spent_floor (d:=d y) w he.le) (catch_hot ..) (add_nonneg hg hg))
       exact h.trans (mul_le_mul_of_nonneg_left (spent_ceil (d:=d y) w he.le) (add_nonneg hg hg))
   have hb:=budget_minor (cap_scale (train_pay hv p k) hp) (fun y=> norm_nonneg (D y)) hh; have hT: Summable W:=by have H : Summable (W-F):=hb.2.1.of_norm; have H' : Summable ((W-F)+F):= H.add ht; rwa [sub_add_cancel] at H'
   rw [← slip_rule p T, ← hT.tsum_sub ht]
   exact (norm_tsum_le_tsum_norm hb.2.1).trans (hb.2.2.trans_eq (mul_right_comm ..))
end YM.WilsonCoeffUV.Winding
