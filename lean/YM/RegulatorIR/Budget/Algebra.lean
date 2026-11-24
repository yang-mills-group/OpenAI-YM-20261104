import YM.RegulatorIR.Budget.Order

/-! Superposition algebra of the folded tensors and estimates. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Budget
open Function Layer Motion Packet Tuple Deck
open scoped Topology ENNReal NNReal BigOperators Classical
variable {X Y Z : Type}{r:ℕ} {P:ℝ}

namespace Deck
variable (A:Deck P X Y)
lemma desk_zero : A.deckSum (0:Packet X r)=0:=by funext x; unfold deckSum; split <;> simp [lodge,dyed]
lemma scroll_zero : A.scroll (0:Packet X r)=0:=by funext x; simp [scroll,Stalk.collect,dyed]
lemma desk_smul (t:ℝ)(T:Packet X r): deckSum A (t • T)=t • deckSum A T:=by
 ext1 i;simp only [Pi.smul_apply,smul_eq_mul];unfold deckSum; split <;> rename_i h
 · simp_rw [Deck.lodge, Deck.dyed, Pi.smul_apply,smul_eq_mul,mul_assoc t,tsum_mul_left]
 rw [mul_zero]
lemma scrolling (t:ℝ)(T:Packet X r):scroll A (t • T)=t • scroll A T:=by
 ext1 i; unfold Deck.scroll Stalk.collect; simp_rw [Deck.dyed,Pi.smul_apply,smul_eq_mul,mul_assoc t,tsum_mul_left]
lemma at_held (u:Tuple Y r)(i:Fin r)(x:X){T:Packet X r}{B:Tariff X}{c:ℝ≥0∞}(h:localQ B T c)(hc:c≠⊤):
    Summable (A.dyed T ∘ (Subtype.val : Nest A u i x→Tuple X r)):=by
 let I := Nest A u i x; let f:I→Hold i x:=fun a=>⟨a.val,a.property.2⟩
 have he:Injective f:= fun _ _ h=>Subtype.ext (Subtype.mk.inj h)
 have hs : Summable (A.dyed T ∘ (Subtype.val : Hold i x → Tuple X r)):= quota_summable (w:=fun p=> B.diameter p.val) (fun p=> B.diameter_unit p.val) <| ne_top_of_le_ne_top hc <| by
    exact (quota_eq (A.dyed T ∘ Subtype.val) (fun p:Tuple.Hold i x=>T p.val) _ (fun p=> A.dyed_cost T p.val)).trans_le (h i x)
 exact (hs.comp_injective he)
lemma desk_sum {f: Z→Packet X r}{B:Tariff X}{c:Z→ℝ≥0∞}(s:Finset Z) (h:∀ i∈s,localQ B (f i) (c i))(hc:∀ i∈s,c i≠⊤):
       deckSum A (∑ i∈s,f i)= ∑ i∈s,deckSum A (f i):= by
 ext1 i; simp only [Finset.sum_apply]; unfold deckSum; split <;> rename_i hr
 · simp_rw [Deck.lodge,Deck.dyed,Finset.sum_apply,Finset.sum_mul]
   apply Summable.tsum_finsetSum; intro a ha; exact A.at_held _ _ _ (h a ha) (hc a ha)
 rw [Finset.sum_const_zero]
lemma scroll_sum {f: Z→Packet X r}(s:Finset Z)(h:∀ i∈s,quota (f i) 1≠⊤):
      scroll A (∑ i∈s,f i)=∑ i∈s,scroll A (f i):=by
 ext1 i; simp_rw [Finset.sum_apply,Deck.scroll,Stalk.collect,Deck.dyed, Finset.sum_apply,Finset.sum_mul]
 apply Summable.tsum_finsetSum; intro a ha
 have hh : Summable (A.dyed (f a)):= quota_summable (w:=1) (fun _=>le_rfl) <| ne_top_of_le_ne_top (h a ha) (quota_dom _ _ fun _=> (A.dyed_cost ..).le)
 exact hh.comp_injective Subtype.val_injective
lemma desk_sup {T U:Packet X r}{B:Tariff X}{c d:ℝ≥0∞}(h:localQ B T c)(hp:c≠⊤)(hh:localQ B U d)(hq:d≠⊤):
      deckSum A (T+U)=deckSum A T+ deckSum A U:=by
 ext1 i; unfold deckSum; simp only [Pi.add_apply]; split <;> rename_i hr
 · simp_rw [Deck.lodge, Deck.dyed,Pi.add_apply,add_mul]; exact Summable.tsum_add (A.at_held _ _ _ h hp) (A.at_held _ _ _ hh hq)
 simp
lemma scroll_sup {T U:Packet X r} (h:quota T 1≠⊤)(hh:quota U 1≠⊤): scroll A (T+U)=scroll A T+scroll A U:=by
 let f : ℕ→Packet X r := fun i=> if i=0 then T else U
 have he : ∀ i∈({0,1}:Finset ℕ),quota (f i) 1≠⊤:= by intro i _; unfold f; split <;> assumption
 simpa [f] using! A.scroll_sum {0,1} he
lemma ready_zero : A.Ready (0:Packet X r):=by intro d x; simp [Deck.dyed]
lemma ready_smul {T:Packet X r} (t:ℝ)(h:A.Ready T): A.Ready (t • T):=by
 apply (A.ready_iff _).mpr; intro v x; simp_rw [Pi.smul_apply,smul_eq_mul,(A.ready_iff _).mp h]; ring
lemma ready_add {T U:Packet X r}(h:A.Ready T)(hh:A.Ready U): A.Ready (T+U):=by
 apply (A.ready_iff _).mpr; intro v x; simp_rw [Pi.add_apply,(A.ready_iff _).mp h,(A.ready_iff _).mp hh,mul_add]
lemma ready_sum {f : Z → Packet X r}(s : Finset Z) (h:∀ i∈s,A.Ready (f i)): A.Ready (∑ i∈s,f i):=by
 induction s using Finset.induction_on with
 | empty=> rw [Finset.sum_empty]; exact A.ready_zero
 | insert i s he ih=> rw [Finset.sum_insert he]; exact A.ready_add (h i (Finset.mem_insert_self ..)) (ih fun i hx=>h i (Finset.mem_insert_of_mem hx))
lemma symm_ready {T:Packet X r}(h:A.Ready T):A.Ready (Packet.symmetry T):= A.ready_smul _ (A.ready_sum _ (fun e _=>A.dyed_perm T e h))
lemma desk_sym {T:Packet X r}{B:Tariff X}{c:ℝ≥0∞}(h:localQ B T c)(hp:c≠⊤)(he:A.Ready T):
    deckSum A (Packet.symmetry T)=Packet.symmetry (deckSum A T):=by
 unfold Packet.symmetry; rw [A.desk_smul, A.desk_sum (c:=fun _=>c) Finset.univ (fun i _=>Packet.local_version B i h) (fun _ _=> hp)]; congr 1; apply Finset.sum_congr rfl;intro i _; ext1 x; exact A.deck_perm T i he x
lemma scroll_sym {T:Packet X r}(h:quota T 1≠⊤): scroll A (Packet.symmetry T)= Packet.symmetry (scroll A T):=by
 unfold Packet.symmetry; rw [A.scrolling,A.scroll_sum _]; congr 1; apply Finset.sum_congr rfl;intro i _;ext1 x; exact A.scroll_perm T i x
 intro i _; exact ne_top_of_le_ne_top h (quota_perm (Tuple.perm X i) T 1).le
end Deck
end YM.RegulatorIR.Budget
