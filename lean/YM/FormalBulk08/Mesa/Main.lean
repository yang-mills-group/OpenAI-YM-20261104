import YM.FormalBulk08.Mesa.Battery

/-! Infinite kinetic op as cover rank2. Do not assume row literally symmetric
outside horizontals; use sym avg (norm no wider). -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Mesa
open Lava Gorge Shore Lattice Laurent Filter Function Lotus Orb Wick Reef Jets Series PowerSeries Stationary Wilson Matrix Next.Free
open Exterior Bloch RG Precision UVExtension.Free Work.F08 Flat
open scoped Topology ENNReal BigOperators Classical ContDiff
variable {r : ℕ} (G : Gauge) {j : ℕ}

def inkling (R : Row (TypeFace 2) (TypeFace 2)) := shadedRows G (composeRows (composeRows (transRows (cobound 1)) R) (cobound 1))
lemma ink_charge (η : ℝ) (hs : 0≤η) : ∃ B : ℝ,0≤B ∧ ∀ R (a : ℝ),0≤a→ Row.strip R η a → Row.strip (inkling G R) η (B*a) ∧ ∀ n:Side, (inkling G R).acts n= patron G (Precision.K (R.acts n)) := by
   obtain ⟨E,hE,H⟩:=delta_budget 1 η
   let t:ℝ:=Fintype.card (TypeFace 2); let B:= t*t*E*E; have ht : 0 ≤ t:= Nat.cast_nonneg _
   refine ⟨B,by unfold B; positivity,fun R a ha h=>?_⟩
   have hU := strip_compose hs (strip_trans H) h; have hx := strip_compose hs hU H
   refine ⟨?_,fun n=>?_⟩
   · apply strip_mono (shades_pay (G:=G) _ (by positivity) hx) le_rfl; apply le_of_eq; unfold B; change t*(t*(E*a)*E)=_;ring
   rw [inkling,shades_acts _ (Row.rights _ _ hx hs),acts_compose hs hU H,acts_compose hs (strip_trans H) h,acts_trans];rfl
lemma ink_delta {η : ℝ} {a b : ℝ} (hs : 0≤η) {R T : Row (TypeFace 2) (TypeFace 2)} (A : R.strip η a) (B : T.strip η b) (ha : 0≤a) (hb : 0≤b) :
    minusRows (inkling G R) (inkling G T)= inkling G (minusRows R T) := by
   obtain ⟨B',-,H⟩:= ink_charge G _ hs
   obtain ⟨hX,F⟩:=H _ _ ha A; obtain ⟨hY,K⟩:=H _ _ hb B
   obtain ⟨hz,J⟩:= H _ _ (add_nonneg ha hb) (strip_minus A B)
   refine bank_injective (Row.rights _ _ (strip_minus hX hY) hs) (Row.rights _ _ hz hs) fun n=>?_
   rw [J,acts_minus hs A B,acts_minus hs hX hY,F,K]; simp_rw [Precision.K,Matrix.mul_sub,Matrix.sub_mul,patron_minus]

-- rank2 pack direct; finite formula
variable {V : Type*}
def couple (M : V→V→ℝ): Tile V 2:= fun w=> -halve (M (w 0) (w 1))
def setkin (R : Row (TypeFace 2) (TypeFace 2)) : Tile (edgeL G) 2:= sand (couple (lands (inkling G R)))
lemma pol_rank [Fintype V] (M : Matrix V V ℝ) : facade 2 (couple M)=crunch M := by
   rw [facade_peels]; simp_rw [facade_peels (Lava.shed (couple M) _)]; unfold crunch; rw [←Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _=>?_; rw [Finset.mul_sum,←Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun j _=>?_
   simp [facade_eq,cards,Lava.shed,couple];ring
lemma kinetic_grade [Fintype V] (M : Matrix V V ℝ) : MvPolynomial.IsHomogeneous (crunch M) 2:= by rw [←pol_rank];apply facade_grade
lemma kinetic_marble [Fintype V] (M : Matrix V V ℝ): marble 2 (crunch M)=sand (couple M) := facade_unique (marble_agate _ _) (agate_sand _) (by rw [marble_grade,sand_facade,MvPolynomial.homogeneousComponent_eq_self (kinetic_grade M),pol_rank])

variable {I : Type*}
lemma up_couple (R : Row I I) : Up (couple (lands R)) := by intro x v; simp [couple,lands]
lemma peg_round {A : Reach I} (w : chain I 2) : wide A w=A.d (w 0) (w 1) := by
   apply le_antisymm _ (reached ..); apply known_wide; intro i j; fin_cases i <;> fin_cases j <;> first|rfl|exact Nat.le_refl _|exact (A.turn (w 1) (w 0)).le|simp [A.self]

lemma peg_anchor {η : ℝ} {D : Reach I} {q : I→I→ℝ} {C : ℝ} (h : Grate D η q C) (e : Grate D η (fun a b=>q b a) C) : Bail D η (couple q) (1/2*C) := by
    refine ⟨mul_nonneg (by norm_num) h.1,fun i a=>?_⟩
    have he (w:chain I 2) : glitter D η (couple q) w=ENNReal.ofReal (1/2)*(shine η (D.d (w 0) (w 1))*‖q (w 0) (w 1)‖ₑ) := by
        unfold glitter couple;rw [peg_round];rw [enorm_neg,←ofReal_norm,half_norm,ENNReal.ofReal_mul (by norm_num),ofReal_norm,mul_left_comm]
    let f (i j:Fin 2) := fun x:pack i a=> x.val j
    have hh (i j : Fin 2) (h:i≠j) : Injective (f i j) := by
       intro v w ht; apply Subtype.ext; funext k; have hk : k=i ∨ k=j:=by omega
       rcases hk with hk|hk <;> subst k; exacts [v.property.trans w.property.symm,ht]
    simp_rw [he];rw [ENNReal.ofReal_mul (by norm_num),ENNReal.tsum_mul_left]; apply mul_le_mul_right
    have hy : i=0 ∨ i=1:= by omega
    rcases hy with h1|h2 <;> subst i
    · refine le_trans ?_ ((ENNReal.tsum_comp_le_tsum_of_injective (hh 0 1 (by decide)) (fun x=> shine η (D.d a x)*‖q a x‖ₑ)).trans (h.2 a)); apply le_of_eq; exact tsum_congr fun v=>by simp_rw [v.property]; rfl
    refine le_trans ?_ ((ENNReal.tsum_comp_le_tsum_of_injective (hh 1 0 (by decide)) (fun x=> shine η (D.d a x)* ‖q x a‖ₑ)).trans (e.2 a)); apply le_of_eq; exact tsum_congr fun v=>by simp_rw [show v.val 1=a from v.property, D.turn _ a]; rfl
lemma peg_charge [Fintype I] {η C : ℝ} {R : Row I I} (h : R.strip η C) (hc : 0 ≤ C) : Bail (fame I) η (couple (lands R)) (1/2*((Fintype.card I)*C)) := by
   have hx:=grad_line _ h hc; apply peg_anchor
   · refine ⟨hx.costs,fun x=>?_⟩; have he:=hx.rows x; simp_rw [linkshine, ← show ∀ (y : Biglot I), (fame I).d y x=size (y.1-x.1) from fun y=>rfl,Reach.turn _ _ x] at he; exact he
   exact ⟨hx.money,hx.columns⟩
lemma setkin_pay {η : ℝ} (hs : 0≤η) : ∃ B : ℝ,0≤B ∧ ∀ R (A : ℝ),0 ≤ A → Row.strip R η A → Bail (fame _) η (setkin G R) (B*A) := by
   obtain ⟨C,hC,H⟩:=ink_charge G _ hs
   let n : ℝ:=Fintype.card (Loc G 1); refine ⟨1/2*n*C,by unfold n; positivity,fun R A h hp=>?_⟩ -- rintro weird
   apply ((peg_charge (H R A h hp).1 (mul_nonneg hC h)).smooth).mono; apply le_of_eq;change 1/2*(n*(C*A))=_;ring
end YM.FormalBulk08.Mesa
