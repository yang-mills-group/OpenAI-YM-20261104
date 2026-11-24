import YM.RegulatorIR.Diagram.Heat

/-! Rank cap and auxiliary time-power cap, no valence truncation assumed on
the result. These bounds permit finite sums rather than a convergence
assumption on all orders. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Diagram
open Function Budget Budget.Layer Budget.Tuple Budget.Packet
open scoped ENNReal Topology BigOperators Classical
variable {I:Type}{r s:ℕ}

lemma symmetric_zero : Packet.IsSym (0:Packet I r):=fun _ _=> rfl
lemma symmetric_add {T U:Packet I r}(h:IsSym T)(hh:IsSym U): IsSym (T+U):=fun e z=> congr_arg₂ (·+·) (h e z) (hh e z)
lemma symmetric_scale {T:Packet I r}(h:IsSym T)(x:ℝ): IsSym (x • T):=fun e z=>congr_arg (x* ·) (h e z)
lemma symmetric_sum {Z:Type*}{v:Z→Packet I r}{s:Finset Z}(h:∀ i∈s,IsSym (v i)): IsSym (∑ i∈s,v i):=by
 induction s using Finset.induction_on with
 | empty=>simp; exact symmetric_zero
 | insert i s he ih=>rw [Finset.sum_insert he];exact symmetric_add (h i (Finset.mem_insert_self ..)) (ih fun j h'=>h _ (Finset.mem_insert_of_mem h'))
lemma heating_sym (K:Layer I I) (T:Ranked I) : IsSym (heating K T r):=symmetric_scale (Packet.is_symmetry _) _
lemma match_sym (K:Layer I I)(T V:Ranked I)(p): IsSym (matchTwo K T V r p):=by
 unfold matchTwo; split_ifs with hr; · subst r; exact symmetric_scale (is_symmetry _) _
 exact symmetric_zero
lemma drift_sym (K:Layer I I)(T V:ℕ→Orders I) (k e r): IsSym (drift K T V k e r):= by
 unfold drift carry force; apply symmetric_sum;intro p _;apply symmetric_sum;intro x _; apply symmetric_sum;exact fun _ _=>match_sym _ _ _ _
lemma heatedSym {V:Orders I}(K:Layer I I) (h:gradedSymmetric V) (table:Bool)(k): gradedSymmetric (logHeat K V table k):=by
 intro e r; cases k with
 | zero=> rw [logHeat_first]; split; exact symmetric_zero; exact h e r
 | succ k=> rw [logHeat_next]; split; exact symmetric_zero; exact symmetric_scale (symmetric_add (heating_sym _ _) (symmetric_scale (drift_sym _ _ _ _ _ _) _)) _
lemma markedSym {F:Orders I} (K:Layer I I)(V:ℕ→Orders I)(h:gradedSymmetric F)(k):gradedSymmetric (markHeat K V F k):=by
 intro e r; cases k with
 | zero=> rw [markHeat_first]; exact h e r
 | succ k=> rw [markHeat_next]; exact symmetric_scale (symmetric_add (heating_sym _ _) (drift_sym _ _ _ _ _ _)) _

lemma loop_zero (K:Layer I I) : loop (0: Packet I (r+2)) K=0:= by funext x;simp [loop,curve]
lemma ray_zero (i:Fin r)(K:Layer I I):ray i 0 K=0:=by funext x;simp [ray,swivel]
lemma sym_zero : Packet.symmetry (0:Packet I r)=0:=by funext x;simp only [symmetry_at,Pi.zero_apply, Finset.sum_const_zero, mul_zero]
lemma knot_left_zero (K:Layer I I)(U:Packet I (s+1)):knot K (0:Packet I (r+1)) U= (0:Packet I (r+s)):=by funext x; simp [knot,splice,lace]
lemma knot_right_zero (K:Layer I I)(T:Packet I (r+1)):knot K T (0:Packet I (s+1))= (0:Packet I (r+s)):=by funext x; simp [knot,splice,ray_zero,lace]
lemma heating_comes {T: Ranked I}{K:Layer I I}(h:heating K T r≠0): T (r+2)≠0:=by intro hv; apply h; rw [heating,hv,loop_zero,sym_zero,smul_zero]
lemma match_comes {T U:Ranked I}{K:Layer I I}{p q:ℕ}(h:matchTwo K T U r (p,q)≠0) : p+q=r ∧ T (p+1)≠0 ∧ U (q+1)≠0:=by
 have hp : p+q=r := by
    by_contra! hp; exact h (by rw [matchTwo, dif_neg hp])
 subst r; refine ⟨rfl,fun hv=>?_,fun hv=>?_⟩
 all_goals apply h;unfold matchTwo; rw [dif_pos rfl]
 · change (_:ℝ) • Packet.symmetry (knot _ (T (p+1)) _)=_; rw [hv,knot_left_zero,sym_zero,smul_zero]
 change (_:ℝ) • Packet.symmetry (knot _ _ (U (q+1)))=_; rw [hv,knot_right_zero,sym_zero,smul_zero]
lemma joins_come {K:Layer I I}{T S:ℕ→Orders I}{k e:ℕ}(h:drift K T S k e r ≠0):
    ∃ i j p q a b:ℕ,i+j=k ∧ p+q=e ∧ a+b=r ∧ T i p (a+1)≠0 ∧ S j q (b+1)≠0 := by
 obtain ⟨⟨i,j⟩,hi,hj⟩:= Finset.exists_ne_zero_of_sum_ne_zero h
 obtain ⟨⟨p,q⟩,hp,hq⟩:= Finset.exists_ne_zero_of_sum_ne_zero hj
 obtain ⟨⟨a,b⟩,ha,hb⟩:= Finset.exists_ne_zero_of_sum_ne_zero hq
 exact ⟨i,j,p,q,a,b,Finset.mem_antidiagonal.mp hi,Finset.mem_antidiagonal.mp hp,match_comes hb⟩

/-- Vacuum and marked rank accounting, including order-zero input restraint. -/
def Within (e:ℕ)(W:Ranked I):Prop:= ∀ r,W r≠0 → r≤e
def Vacuum (V:Orders I):Prop:= ∀ e r,V e r≠0 → 0<e ∧ r≤ e+2
lemma heated_cap (K:Layer I I) (V:Orders I) (h:Vacuum V) (f:Bool) (e r k:ℕ) (hv:logHeat K V f k e r≠0): 0<e ∧ r≤ e+2 ∧ 2*k+r ≤ 3*e:= by
 induction k using Nat.strong_induction_on generalizing r e with
 | _ k ih=>
   cases k with
   | zero =>
       rw [logHeat_first] at hv; split_ifs at hv; · exact (hv rfl).elim
       obtain ⟨hp,hq⟩:= h e r hv; omega
   | succ j=>
       let W := logHeat K V f
       rw [logHeat_next] at hv; split_ifs at hv; · exact (hv rfl).elim
       by_cases hx:heating K (W j e) r=0
       · change ((_ : ℝ) • (heating K (W j e) r + (2:ℝ)⁻¹ • drift K W W j e r)) ≠ 0 at hv
         rw [hx, zero_add] at hv
         obtain ⟨i,l,p,q,a,b,H,U,S,hT,hV⟩:= joins_come (K:=K) (r:=r) (e:=e) (T:=W) (S:=W) (k:=j) (fun h=>hv (by rw [h,smul_zero,smul_zero]))
         have hI:= ih i (by omega) p (a+1) hT; have hJ:= ih l (by omega) q (b+1) hV; omega
       have he:= ih j (by omega) e (r+2) (heating_comes hx); omega
lemma marked_cap (m:ℕ)(K:Layer I I)(V:Orders I)(h:Vacuum V)(T:Orders I)(hh:∀ e,Within (e+m) (T e))(f:Bool)(e r k:ℕ):
    markHeat K (logHeat K V f) T k e r≠0→ r≤e+m ∧ 2*k+r≤ 3*e+m:= by
 induction k using Nat.strong_induction_on generalizing r e with
 | _ k ih=>
   cases k with
   | zero => rw [markHeat_first];intro h; have he:= hh _ _ h;omega
   | succ j=>
       rw [markHeat_next];intro hV; let S:= markHeat K (logHeat K V f) T
       by_cases ht:heating K (S j e) r=0
       · change (_ :ℝ) • (heating K (S j e) r + drift K S _ j e r) ≠ 0 at hV
         rw [ht,zero_add] at hV
         obtain ⟨i,l,p,q,a,b,H,U,M,hx,hF⟩:= joins_come (K:=K) (T:=S) (S:=logHeat K V f) (e:=e) (r:=r) (k:=j) (fun hp=>hV (by rw [hp,smul_zero]))
         have hI:= ih i (by omega) p (a+1) hx; have hJ:= heated_cap K V h f q (b+1) l hF; omega
       have hI:= ih j (by omega) e (r+2) (heating_comes ht); omega
end YM.RegulatorIR.Diagram
