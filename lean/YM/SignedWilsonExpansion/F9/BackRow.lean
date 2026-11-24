import YM.SignedWilsonExpansion.F9.Board
/-!
# Back solve along one activated tableau (length price)
It is important not to use a `max ‖T(m)⁻¹‖` bill raised to the window
length. Solve along each weight; only charge off-grade arrows. Counts the
whole rank. This file uses abstract ℝ rows throughout.
-/
set_option autoImplicit false
set_option maxHeartbeats 640000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Filter Function Matrix Lattice RG Bank Realm Shard
open scoped Topology BigOperators Classical
variable {m n h k e r i l q b:ℕ}{τ:Type*}{M A x:ℝ}{D V:Credit}
section
variable [Fintype τ]
-- positive diagonal and neutral on ties of same weight.
structure Down (t:τ→ℕ)(P:Matrix τ τ ℝ)(X:ℝ):Prop where
   self (i:τ): 1 ≤ P i i
   value (i j:τ): ‖P i j‖≤ X
   ties (i j:τ): t i≤ t j→ i≠j → P i j=0
lemma Down.step (t:τ→ℕ)(P:Matrix τ τ ℝ){X Y Z Ω:ℝ}(p:Down t P Ω)(he:0≤X)(hq:0≤ Ω)(φ:τ→ℝ)(f:τ→ℝ)(v:τ)
    (hx:∀ u,t u<t v→‖φ u‖≤X)(hy:‖f v‖≤Y)(ht:‖f v-(P*ᵥ φ) v‖≤Z):
    ‖φ v‖ ≤ Y+(Z+(Fintype.card τ:ℝ)*Ω*X):=by
    let T (i:τ):=P v i*φ i; let S:= Finset.univ.erase v; let V:=∑ i∈S,T i
    have hB : ‖V‖≤(Fintype.card τ:ℝ)*Ω*X:=by
       have H (i:τ) (h:i∈S): ‖T i‖≤Ω*X:=by
           by_cases h:t i<t v
           · exact le_trans (le_of_eq (norm_mul _ _)) (mul_le_mul (p.value ..) (hx i h) (norm_nonneg _) hq)
           unfold T; rw [p.ties v i (by omega) (Ne.symm (Finset.mem_erase.mp ‹_›).1),zero_mul,norm_zero]; exact mul_nonneg hq he
       refine (norm_sum_le ..).trans ((Finset.sum_le_sum H).trans ?_); rw [Finset.sum_const,nsmul_eq_mul,mul_assoc]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ S) (mul_nonneg hq he)
    have hv: ‖T v‖≤Y+(Z+(Fintype.card τ:ℝ)*Ω*X):= calc
       ‖T v‖ = ‖f v-((f v-(P*ᵥφ) v)+V)‖:= by rw [show (P*ᵥφ) v=T v+V from (Finset.add_sum_erase _ T (Finset.mem_univ v)).symm]; apply congr_arg norm; abel
       _ ≤ _ := (norm_sub_le ..).trans (add_le_add hy ((norm_add_le ..).trans (add_le_add ht hB)))
    exact (le_mul_of_one_le_left (norm_nonneg _) ((p.self v).trans (le_abs_self _))).trans ((le_of_eq ((norm_mul _ _).symm)).trans hv)

private lemma envelope {J:ℕ→ℝ}{X Y:ℝ}(h:J m≤ X)(p:∀ i,m ≤ i→ i<l → J (i+1)≤ J i+Y){i:ℕ}(he:m ≤ i)(hx:i≤l): J i≤ X+((i-m:ℕ):ℝ)*Y:=by
    induction he with
    | refl=> simpa using h
    | @step i he ih=>
        refine (p i he (by omega)).trans ((add_le_add_left (ih (by omega)) Y).trans (le_of_eq ?_)); rw [show i+1-m=(i-m)+1 by have ht:m≤ i:=he; omega,Nat.cast_add,Nat.cast_one]; ring

/-- Horizon d covers all weights strictly below the number d. -/
lemma triangular (t:τ→ℕ)(d:ℕ)(B Z:Credit) : ∃ W:Credit,∀ X≥(1:ℝ), ∀ M≥(0:ℝ),∀ i l:ℕ,i≤l→ ((l-i:ℕ):ℝ)≤X→∀ (P:ℕ→Matrix τ τ ℝ)(A:ℕ→τ→ℝ),
    (∀ j,(i≤j∧ j<l) → Down t (P j) (Z.buy X)) → (∀ j k,i≤j → j<l → ‖A j k-(P j *ᵥ A (j+1)) k‖ ≤ B.buy X * M) → (∀ k,‖A i k‖≤ B.buy X*M) →
    ∀ j k,t k<d → i≤j→ j≤l → ‖A j k‖ ≤ W.buy X*M:=by
    induction d with
    | zero=> exact ⟨Credit.unit,fun X ht M _ _ _ _ _ P A _ _ _ a b p _ _=>by omega⟩
    | succ d ih=>
       obtain ⟨W,w⟩:= ih; let C:ℝ:= Fintype.card τ; let V:= B.plus (((pur C).prodC Z).prodC W)
       refine ⟨B.plus (Credit.leanC.prodC V),fun X ht M he i l il hl P A Hp Hv Hz j k p q u=>?_⟩; have h (a:ℕ) (ha:i≤a)(hb:a<l) : ‖A (a+1) k‖≤ ‖A a k‖+ V.buy X*M:= by
           have hw:0≤ W.buy X*M:=mul_nonneg (zero_le_one.trans (W.purchase ht)) he
           have hz:0≤Z.buy X:= zero_le_one.trans (Z.purchase ht)
           refine ((Hp a ⟨ha,hb⟩).step t (P a) hw hz (A (a+1)) _ k (fun b y=> w X ht M he i l il hl P A Hp Hv Hz _ b (by omega) (by omega) hb) le_rfl (Hv a k ha hb)).trans (add_le_add_right ?_ _)
           unfold V; apply le_trans _ (mul_le_mul_of_nonneg_right (Credit.fuel _ _ ht) he); rw [add_mul (B.buy X),Credit.products,Credit.products] -- fix
           refine add_le_add_right ?_ _; exact (le_of_eq (show _*(W.buy X*M)= (C*Z.buy X*W.buy X)*M from by unfold C; ring)).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pure_goal C X) hz) (zero_le_one.trans (W.purchase ht))) he)
       have he' : ((j-i:ℕ):ℝ)≤X:= (Nat.cast_le.mpr (show j-i≤ l-i by omega)).trans hl
       have hp':0≤ V.buy X*M:= mul_nonneg (zero_le_one.trans (V.purchase ht)) he
       have hg:= envelope (J:=fun i=>‖A i k‖) (Hz k) h q u
       apply hg.trans ((add_le_add_right (mul_le_mul_of_nonneg_right he' hp') _).trans ?_)
       rw [← mul_assoc X,← add_mul]; apply mul_le_mul_of_nonneg_right _ he; exact le_trans (le_of_eq (show B.buy X+X*V.buy X=B.buy X+(Credit.leanC.prodC V).buy X from by rw [Credit.products,Credit.lean_cost])) (Credit.fuel B _ ht)

lemma oneRow (t:τ→ℕ)(d:ℕ)(ht:∀i,t i<d)(B Z:Credit): ∃ W: Credit,∀ X≥(1:ℝ),∀ M≥(0:ℝ),∀ (P:Matrix τ τ ℝ)(A:τ→ℝ),(Down t P (Z.buy X)) → (∀ i,‖(P*ᵥA) i‖≤B.buy X*M)→ ∀ i,‖A i‖≤ W.buy X*M:=by
    obtain ⟨W,w⟩:= triangular t d B Z; refine ⟨W,fun X hp M ha P A hf hz i=>?_⟩; refine w X hp M ha 0 1 (by omega) (by simpa using hp) (fun _=>P) (fun t=> if t=0 then P*ᵥ A else A) (fun _ _=>hf) ?_ ?_ 1 i (ht i) (by omega) (by omega)
    · intro j k v h; rw [show j=0 by omega]; change ‖(P*ᵥ A) k-(P*ᵥA) k‖≤ _; rw [sub_self,norm_zero]; exact mul_nonneg (zero_le_one.trans (B.purchase hp)) ha
    exact hz
end
end YM.WilsonCoeffUV.Mer.Xa
