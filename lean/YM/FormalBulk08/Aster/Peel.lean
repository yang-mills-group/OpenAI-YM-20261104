import YM.FormalBulk08.Aster.Stern

/-! Emerson. Adjacent ratio transmission at exactly degree endpoints. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Aster
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free PowerSeries
open scoped Topology ENNReal BigOperators Classical
variable {I:Type}{e r m n:ℕ}(τ:Time I)(δ:I→ℝ)
def Priced (T U:I→Pence)(e:ℕ): Prop:= ∀ j≤ e,Pact τ δ (fun i=>coeff j (T i)) (fun i=>coeff j (U i))
lemma Priced.constant (z:Pence)(e:ℕ): Priced τ δ (fun _=>z) (fun _=>z) e:= fun j _=> Pact.coin τ δ (coeff j z)
variable {τ δ}{T U S V:I→Pence}
lemma Priced.le (h:Priced τ δ T U e)(he:r ≤ e): Priced τ δ T U r:=fun i hi=> h i (hi.trans he)
lemma Priced.pivot (h:Priced τ δ T U e): Pact τ δ (fun i=>coeff e (T i)) (fun i=>coeff e (U i)):= h e le_rfl
lemma Priced.less (h:Priced τ δ T U e)(p:Priced τ δ S V e): Priced τ δ (fun i=> T i-S i) (fun i=> U i-V i) e:= by intro j hj;simp_rw [map_sub];exact (h j hj).minus (p j hj)
lemma Priced.times (h:Priced τ δ T U e)(p:Priced τ δ S V e): Priced τ δ (fun i=> T i*S i) (fun i=> U i*V i) e:= by
    intro j hj; simp_rw [coeff_mul]; apply pact_sums _; intro i hi;rw [Finset.mem_antidiagonal] at hi; exact (h i.1 (by omega)).times (p i.2 (by omega))
lemma Priced.pows (h:Priced τ δ T U e)(r:ℕ): Priced τ δ (fun i=> T i ^r) (fun i=> U i ^r) e:= by
    induction r with
    | zero=> simp only [pow_zero]; exact Priced.constant τ δ 1 e
    | succ r ih=>simp_rw [pow_succ]; exact ih.times h
lemma Priced.by_order (h:Priced τ δ S V e)(p:Priced τ δ T U e)(he:∀ i,coeff 0 (T i)=0)(ht:∀ i, coeff 0 (U i)=0): Priced τ δ (fun i=> (S i).subst (T i)) (fun i=> (V i).subst (U i)) e:= by
    intro j hj; simp_rw [subst_coeff (he _) _ e j hj, subst_coeff (ht _) _ e j hj]; apply pact_sums _;intro i hi; rw [Finset.mem_range] at hi;exact (h i (by omega)).times (p.pows i j hj)
lemma Priced.exp (p:Priced τ δ T U e)(he:∀ i,coeff 0 (T i)=0)(ht:∀ i,coeff 0 (U i)=0): Priced τ δ (fun i=>expan (T i)) (fun i=> expan (U i)) e:= (Priced.constant τ δ (PowerSeries.exp ℝ) e).by_order p he ht
lemma Priced.log (p:Priced τ δ T U e)(he:∀ i,Fresh (T i))(ht:∀ i,Fresh (U i)): Priced τ δ (fun i=> covelog (T i)) (fun i=> covelog (U i)) e:= (Priced.constant τ δ (stem ℝ) e).by_order (p.less (Priced.constant τ δ 1 e)) (fun i=>by rw [map_sub, he i,coeff_zero_one,sub_self]) (fun i=>by rw [map_sub, ht i,coeff_zero_one,sub_self])
-- inverse by grade
lemma inv_point (P Q:Pence)(hp:Fresh Q)(h:P*Q=1)(e): coeff e P=coeff e (1:Pence) - ∑ i∈(Finset.antidiagonal e).erase (e,0),coeff i.1 P*coeff i.2 Q:= by
    apply eq_sub_of_add_eq; rw [←h]
    rw [coeff_mul,←Finset.add_sum_erase (Finset.antidiagonal e) _ (a:= (e,0)) (by simp),hp,mul_one]
lemma Priced.return (h:Priced τ δ T U e)(he:∀ i,Fresh (T i))(hh:∀ i,Fresh (U i))(a: ∀ i,S i*T i=1)(b:∀ i,V i*U i=1): Priced τ δ S V e:= by
    intro j hj; induction j using Nat.strong_induction_on with
    | _ j ih =>
      rw [show (fun i=>coeff j (S i))=_ from funext fun i=>inv_point _ _ (he i) (a i) _,show (fun i=>coeff j (V i))=_ from funext fun i=>inv_point _ _ (hh i) (b i) _]; refine (Pact.coin τ δ _).minus (pact_sums _ fun v hv=>?_); obtain ⟨hp,hx⟩:=Finset.mem_erase.mp hv;rw [Finset.mem_antidiagonal] at hx; exact (ih v.1 (by rcases v;simp at hp;omega) (by omega)).times (h _ (by omega))
lemma Priced.next (h:Priced τ δ T U e)(he:∀ i,Fresh (T i))(hp:∀ i,Fresh (U i)): Priced τ δ (fun i=> nextU (T i)) (fun i=> nextU (U i)) e := by
    have hg i:=violet_height _ (he i); have hh i:=violet_height _ (hp i)
    have hu (p:Pence)(hP:Fresh p): coeff 0 (C (1/2:ℝ)*covelog p)=0:=by rw [coeff_C_mul,covelog_rank hP,mul_zero]
    have ht: Priced τ δ (fun i=>violet (T i)) (fun i=>violet (U i)) e:= ((Priced.constant τ δ (C (1/2:ℝ)) e).times (h.log he hp)).exp (fun i=>hu _ (he i)) (fun i=>hu _ (hp i))
    exact ht.return hg hh (fun i=> (mul_comm ..).trans (next_foot _ (he i))) (fun i=> (mul_comm ..).trans (next_foot _ (hp i)))
lemma Priced.goods (h:Priced τ δ T U e)(he:∀ i,Fresh (T i))(hp:∀ i,Fresh (U i)): Priced τ δ (fun i=>bookH (T i)) (fun i=>bookH (U i)) e ∧ Priced τ δ (fun i=> bookU (T i)) (fun i=> bookU (U i)) e:= by
    have ht:=h.next he hp
    have hv (j:ℕ)(hj:j≤e) : Priced τ δ (fun i=>bookH (T i)) (fun i=>bookH (U i)) j := by
       induction j with
       | zero=>
         intro l hl; have h:l=0:=by omega
         subst l; simp_rw [show ∀ i, coeff 0 (bookH (T i))=1 from fun i=> book_fresh _,show ∀ i,coeff 0 (bookH (U i))=1 from fun i=> book_fresh _]; exact Pact.coin τ δ 1
       | succ j ih=>
         have hb:=ih (show j≤e by omega)
         have hh: Priced τ δ (fun i=> runic (T i)) (fun i=>runic (U i)) (j+1):= by
            intro i hi;cases i with
            | zero=> simp_rw [runic_phi];exact Pact.coin τ δ 0
            | succ i=> simp_rw [←forward_green, coeff_succ_X_mul]; apply hb i (by omega)
         have he' := (ht.le hj).by_order hh (fun i=>runic_phi (T i)) (fun i=>runic_phi (U i))
         exact he'.return (fun i=>by rw [←blue_credit]; exact book_guard _) (fun i=>by rw [←blue_credit]; exact book_guard _) (fun i=>book_credit (T i)) (fun i=>book_credit (U i))
    exact ⟨hv e le_rfl, (hv e le_rfl).return (fun i=> book_fresh (T i)) (fun i=>book_fresh (U i)) (fun i=>(mul_comm ..).trans (book_equal (T i))) (fun i=>(mul_comm ..).trans (book_equal (U i)))⟩
lemma Priced.income (h:Priced τ δ T U e)(p:Priced τ δ S V e)(m n r:ℕ)(he:m-n≤ e): Pact τ δ (fun i=>Wine.bill (T i) (S i) m n r) (fun i=>Wine.bill (U i) (V i) m n r) := ((h.pows n).times (p.pows r)) _ he
end YM.FormalBulk08.Aster
