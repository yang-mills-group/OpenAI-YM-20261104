import YM.SignedWilsonExpansion.F9.BackRow
import YM.Extra.SOURCE_HISTORIES.Sizes
import YM.Push.LOCAL_SPLITTING.Leading
/-!
Threshold-physical `.ride` systems. Fixed weight (NOT order) prices.
-/
set_option autoImplicit false
set_option maxHeartbeats 640000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa.FetchP
open Filter Function Matrix Lattice RG Bank Realm Shard
open scoped Topology BigOperators Classical
variable {m n h k e r i l q b:ℕ}{τ:Type*}{M A x:ℝ}{D V:Credit}
section
variable [Fintype τ]
-- positive diagonal and neutral on ties of same weight.
structure Down (t:τ→ℕ)(P:Matrix τ τ ℂ)(X:ℝ):Prop where
   self (i:τ): 1 ≤ ‖P i i‖
   value (i j:τ): ‖P i j‖≤ X
   ties (i j:τ): t i≤ t j→ i≠j → P i j=0
lemma Down.step (t:τ→ℕ)(P:Matrix τ τ ℂ){X Y Z Ω:ℝ}(p:Down t P Ω)(he:0≤X)(hq:0≤ Ω)(φ:τ→ℂ)(f:τ→ℂ)(v:τ)
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
    exact (le_mul_of_one_le_left (norm_nonneg _) (p.self v)).trans ((le_of_eq ((norm_mul _ _).symm)).trans hv)

private lemma envelope {J:ℕ→ℝ}{X Y:ℝ}(h:J m≤ X)(p:∀ i,m ≤ i→ i<l → J (i+1)≤ J i+Y){i:ℕ}(he:m ≤ i)(hx:i≤l): J i≤ X+((i-m:ℕ):ℝ)*Y:=by
    induction he with
    | refl=> simpa using h
    | @step i he ih=>
        refine (p i he (by omega)).trans ((add_le_add_left (ih (by omega)) Y).trans (le_of_eq ?_)); rw [show i+1-m=(i-m)+1 by have ht:m≤ i:=he; omega,Nat.cast_add,Nat.cast_one]; ring

/-- Horizon d covers all weights strictly below the number d. -/
lemma triangular (t:τ→ℕ)(d:ℕ)(B Z:Credit) : ∃ W:Credit,∀ X≥(1:ℝ), ∀ M≥(0:ℝ),∀ i l:ℕ,i≤l→ ((l-i:ℕ):ℝ)≤X→∀ (P:ℕ→Matrix τ τ ℂ)(A:ℕ→τ→ℂ),
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

lemma oneRow (t:τ→ℕ)(d:ℕ)(ht:∀i,t i<d)(B Z:Credit): ∃ W: Credit,∀ X≥(1:ℝ),∀ M≥(0:ℝ),∀ (P:Matrix τ τ ℂ)(A:τ→ℂ),(Down t P (Z.buy X)) → (∀ i,‖(P*ᵥA) i‖≤B.buy X*M)→ ∀ i,‖A i‖≤ W.buy X*M:=by
    obtain ⟨W,w⟩:= triangular t d B Z; refine ⟨W,fun X hp M ha P A hf hz i=>?_⟩; refine w X hp M ha 0 1 (by omega) (by simpa using hp) (fun _=>P) (fun t=> if t=0 then P*ᵥ A else A) (fun _ _=>hf) ?_ ?_ 1 i (ht i) (by omega) (by omega)
    · intro j k v h; rw [show j=0 by omega]; change ‖(P*ᵥ A) k-(P*ᵥA) k‖≤ _; rw [sub_self,norm_zero]; exact mul_nonneg (zero_le_one.trans (B.purchase hp)) ha
    exact hz
end
open Labels Extra.Histories Work.G08
variable {G:Gauge} (F:Labels.Frame G h) -- {G} implicit? set false
abbrev RankW (t:F.Coeff →ₗ[ℂ] F.Coeff) (Ω:ℝ): Prop:= Down (fun i=>(F.grades i).1) (fun i j:F.Index=> t (Size.axis F j) i) Ω
abbrev ledgerC (P:ℕ→F.Coeff →ₗ[ℂ] F.Coeff) (Ω:ℝ): Prop:= ∀ k∈ Finset.Ico i l,RankW F (P k) Ω -- undeclared `i l` automatic inferred?
-- write explicit
abbrev debt (i l:ℕ) (V:ℕ→F.Coeff)(P:ℕ→F.Coeff →ₗ[ℂ] F.Coeff)(Ω:ℝ): Prop:=∀ k∈ Finset.Ico i l,F.coeffSize (V k-P k (V (k+1)))≤ Ω
abbrev peak (i l:ℕ)(V:ℕ→F.Coeff)(Ω:ℝ): Prop:= ∀ j∈ Finset.Icc i l,F.coeffSize (V j) ≤ Ω
lemma bound_ledger (B:Credit): ∃ Z:Credit,∀ Y≥(1:ℝ),∀ ε≥(0:ℝ),∀ i l:ℕ,i≤l→ ((l-i:ℕ):ℝ)≤Y→∀ (V:ℕ→F.Coeff)(P:ℕ→F.Coeff →ₗ[ℂ] F.Coeff), ledgerC F P (B.buy Y) (i:=i) (l:=l) → debt F i l V P ε→
     peak F i l V (Z.buy Y*(F.coeffSize (V i)+ε)):=by
    obtain ⟨z,hZ⟩:= triangular (fun i:F.Index=>(F.grades i).1) (h+1) Credit.unit B
    let T:= Fintype.card F.Index; refine ⟨(pur T).prodC z, fun Y hy ε hp i l il hj V P p q b hb=>?_⟩
    let A(k:ℕ): Matrix F.Index F.Index ℂ:=fun i j=>P k (Size.axis F j) i
    have ht: 0≤ F.coeffSize (V i):=size_nonneg ..; let X:= F.coeffSize (V i)+ε; have hx:0≤X:=add_nonneg ht hp
    have h0(k:F.Index)(v:F.Coeff): ‖v k‖≤ F.coeffSize v:= (norm_le_pi_norm v k).trans (Size.norm_le F v)
    have hr (k:ℕ) (x:F.Coeff): P k x=A k *ᵥ x:= funext (fun t=> (Push.Local.matrix_coeff ..).symm)
    have hs (k): ‖V b k‖≤ z.buy Y*X:=by
       apply hZ Y hy X hx i l il hj A V (fun k hk=>p k (Finset.mem_Ico.mpr hk)) _ _ b k (Nat.lt_succ_of_le (F.bound k)) (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hb).2
       · intro j k hy hw; rw [←hr, Credit.unit_cost,one_mul]; exact (h0 k (V j-P j (V (j+1)))).trans ((q j (Finset.mem_Ico.mpr ⟨hy,hw⟩)).trans (le_add_of_nonneg_left ht))
       intro k; rw [Credit.unit_cost, one_mul]; exact (h0 _ _).trans (le_add_of_nonneg_right hp)
    rw [Credit.products]; exact (Size.le_norm F _).trans ((mul_le_mul (pure_goal (T:ℝ) _) ((pi_norm_le_iff_of_nonneg (mul_nonneg (zero_le_one.trans (z.purchase hy)) hx)).mpr hs) (norm_nonneg _) (zero_le_one.trans (Credit.purchase (pur T) hy))).trans_eq (mul_assoc ..).symm)
lemma hLease (a b:ℕ) (hb:a≤b)(V:ℕ→F.Coeff): ∃ Y≥(0:ℝ), peak F a b V Y ∧ ∃ j∈ Finset.Icc a b,F.coeffSize (V j)=Y:=by
    have hp:(Finset.Icc a b).Nonempty:= ⟨a,Finset.mem_Icc.mpr ⟨le_rfl,hb⟩⟩; obtain ⟨i,t,h⟩:= Finset.exists_max_image (Finset.Icc a b) (fun i=> F.coeffSize (V i)) hp; exact ⟨_,size_nonneg ..,h,i,t,rfl⟩
-- inverse-stability irrespective of magnitude. ε here is an ABSOLUTE relative speed per-step and eventual after K/f fixed.
lemma bound_ledger' (B:Credit): ∃ e Z:Credit, ∀ Y≥(1:ℝ),∀ ε≥(0:ℝ),e.buy Y*ε≤1/2 → ∀ i l:ℕ,i≤l→ ((l-i:ℕ):ℝ)≤Y → ∀ (V:ℕ→F.Coeff)(P:ℕ→F.Coeff →ₗ[ℂ] F.Coeff), ledgerC F P (B.buy Y) (i:=i) (l:=l)→
       (∀ k∈ Finset.Ico i l,F.coeffSize (V k-P k (V (k+1))) ≤ ε * (F.coeffSize (V k)+F.coeffSize (V (k+1)))) → peak F i l V (Z.buy Y*F.coeffSize (V i)) := by
    obtain ⟨z,hZ⟩:= bound_ledger F B; let Z:=z.plus z; refine ⟨Z,Z,fun Y hy ε hp he i l il hr V P p h=>?_⟩; obtain ⟨b,hb,h₁,j,hj,h₂⟩:= hLease F i l il V; have hε:=hp
    have hv: peak F i l V (z.buy Y*(F.coeffSize (V i)+ ε*(b+b))):= hZ Y hy _ (mul_nonneg hε (add_nonneg hb hb)) _ _ il hr V P p (fun j h'=> let ⟨x,w⟩:= Finset.mem_Ico.mp h'; (h j h').trans (mul_le_mul_of_nonneg_left (add_le_add (h₁ j (Finset.mem_Icc.mpr ⟨x,w.le⟩)) (h₁ (j+1) (Finset.mem_Icc.mpr ⟨by omega,w⟩))) hε))
    have H': b≤z.buy Y * ( F.coeffSize (V i) + ε*(b+b)):=h₂ ▸ hv j hj; have hn: (z.buy Y+z.buy Y)*ε≤1/2:= (mul_le_mul_of_nonneg_right (Credit.fuel _ _ hy) hε).trans he
    have hh:b≤Z.buy Y* F.coeffSize (V i):=by unfold Z; nlinarith only [H',mul_le_mul_of_nonneg_right hn hb, mul_le_mul_of_nonneg_right (Credit.fuel z z hy) (size_nonneg F (V i))]
    exact fun j hj=> (h₁ j hj).trans hh
end YM.WilsonCoeffUV.Mer.Xa.FetchP
