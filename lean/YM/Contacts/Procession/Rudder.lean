import YM.Contacts.Procession.Wake
/-! # Shift law for one mark, retained leading propagation -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Procession.Sun
open Function Set Filter Pulse Matrix MeasureTheory Finset
open Milling Milling.Forge Pulse.Form
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff
variable {X Y α E : Type}{n i v w r t k j l:ℕ} [Fintype α] (g:α→α→ℝ) {A F Y': House α}
def shiftA (t:ℕ)(F:House X): House X:= fun i=> if t≤ i then F (i-t) else 0
abbrev paceA (t:ℕ)(F:GridTime X): GridTime X := fun i=> shiftA t (F i)
-- generic proof one side convolution
lemma haulV [AddCommMonoid X](f: ℕ→ℕ→X): (∑ i∈antidiagonal t,if k ≤ i.1 then f (i.1-k) i.2 else 0)=if k ≤ t then ∑ i∈antidiagonal (t-k), f i.1 i.2 else 0:= by
   split -- likely split of nested ite sum? rw RHS
   next h=>
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, show t.succ=k+(t-k).succ from by omega, Finset.sum_range_add, Finset.sum_eq_zero,zero_add]; swap; · intro u hu; have he:k>u:=mem_range.mp hu; exact if_neg (not_le.mpr he)
    apply sum_congr rfl; intro i hi; change (if k ≤ k+i then _ else _) = _; rw [if_pos (by omega)]; exact congr_arg₂ f (by simp) (by simp; omega)
   exact sum_eq_zero fun i hi=> if_neg (by have ht:=mem_antidiagonal.mp hi; omega)
lemma pact (A H:GridTime α): convK g (paceA k A) H t i= if k≤ t then convK g A H (t-k) i else 0 := by
   unfold convK; let f b a := ∑ q∈antidiagonal i, crossH g (A q.1 b) (H q.2 a); rw [← haulV f]; apply sum_congr rfl; intro r _; unfold f paceA shiftA; split_ifs <;> simp [*] -- edit
lemma packed (A H: GridTime α): convK g A (paceA k H) t i= if k≤ t then convK g A H (t-k) i else 0 := by
   unfold convK; rw [← Finset.Nat.sum_antidiagonal_swap (n:=t), ← Finset.Nat.sum_antidiagonal_swap (n:=t-k)]; let f a b:= ∑ q∈ antidiagonal i, crossH g (A q.1 b) (H q.2 a); erw [← haulV f]; apply sum_congr rfl; intro p _; unfold f; change (∑ q∈antidiagonal i, crossH g (A q.1 p.2) (shiftA k (H q.2) p.1))=_ -- edit
   unfold shiftA; split_ifs <;> simp [*]
lemma fact (V H U F:GridTime α)(he:∀ p≤ i,∀ q≤t, H p q=V p q)(h:∀ p ≤ i,∀ q≤ t, U p q= F p q): convK g H U t i=convK g V F t i:= by refine sum_congr rfl fun p hp=>sum_congr rfl fun q hq=> ?_; have x:=mem_antidiagonal.mp hp; have y:= mem_antidiagonal.mp hq; rw [he q.1 (by omega) _ (by omega),h q.2 (by omega) _ (by omega)]
lemma devoted (A V W B: GridTime α) : convK g (A+V) (W+B) i t= convK g A W i t + convK g A B i t + (convK g V W i t + convK g V B i t) := by simp_rw [convK,Pi.add_apply,map_add,LinearMap.add_apply,sum_add_distrib]; abel
lemma pledge (A H: GridTime α)(he:i<k+k) : convK g (paceA k A) (paceA k H) i t=0:= by rw [pact]; split; rw [packed, if_neg (by omega)]; rfl
lemma arising (f g': GridTime α)(h:t<k+k) : wake g (f+paceA k g') t i=wake g f t i + if k≤ t then indus g f g' (t-k) i else 0:= by
   rw [wake_comp,wake_comp,Pi.add_apply,Pi.add_apply,map_add,devoted, pledge _ _ _ h, pact,packed]; unfold paceA shiftA; split_ifs <;> simp [*] <;> first | (unfold indus; abel) | skip
lemma inlet (he:i ≤ j) (X:ℕ): ((j:ℕ)+X-j)=X := by omega -- unneeded
lemma statute (F V:House α)(hi:i<k+k) (he:∀ t≤ i, A t=F t+shiftA k V t) : gathering g A j i=gathering g F j i+paceA k (walk g F V) j i:= by
    induction j using Nat.strongRecOn generalizing i with| _ j ih=>
      cases j with
      | zero=> rw [gathering_start,gathering_start, paceA,walk_start]; exact he i le_rfl
      | succ j=>
        let H:=gathering g F; let U:=walk g F V; have he(p:ℕ)(hp:p≤j)(q:ℕ)(hq:q≤ i): gathering g A p q= (H+paceA k U) p q := ih p (by omega) (by omega) (fun d hd=> he d (hd.trans hq));
        have hw : wake g (gathering g A) i j= wake g H i j + if k≤ i then indus g H U (i-k) j else 0:= by rw [← arising _ _ _ hi,wake_comp,wake_comp, fact g _ _ _ _ he he, he j le_rfl _ le_rfl]
        rw [gathering_next, gathering_next];
        -- want ext & hw
        let C:= (((j+1:ℕ):ℝ)⁻¹); change C • (wake _ _ _ _)= C • wake g H _ _ + _; rw [hw,smul_add]; apply congr_arg _; unfold paceA shiftA; split_ifs; rw [walk_step]; rw [smul_zero]
end YM.Contacts.Procession.Sun
