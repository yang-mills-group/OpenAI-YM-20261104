import YM.Comparison.Density.Payload.Testing
/-!
Represented marked exponent. Count sites, supports, tests and all
roots INSIDE the budget. Constants also stay on this tape (not
masked; still attached to positions through `static`). Do not
push them as mask-
indicator terms unless exactly compensating the change. Existence of
a global hit sum for this finite, but not bounded in size, instance of
a represented density is NOT a uniform budget on the normalization of
observables.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density
open Testing Markers Marker RG Multi Lattice Function Filter
open Wilson MeasureTheory
open scoped Matrix.Norms.Frobenius Topology BigOperators
variable {V : Type} [DecidableEq V] {R : Census V} {G : Gauge} {n : Side}
variable {X : V→Type} [∀ v, NormedAddCommGroup (X v)] [∀ v, NormedSpace ℂ (X v)]

structure Readers (V : Type) (X : V→Type) (n : Side) where
  source : Origin V n
  locus : Region X n

abbrev Address (R : Census V) := Hot R × ℕ

structure Registers (R : Census V) (X : V→Type) (G : Gauge) (n : Side) where
  static : Address R → Support n
  constant : Address R → Cross X → ℂ
  sites : Address R → Support n
  body : Address R → Cross X → Config G n → ℂ

def Freight (p : BudgetPoint) (w : V→ℝ) (Y : Address R→ Support n) (a : Address R→ℝ) (b : ℝ) :=
    0 ≤ b ∧ (∀ i,0≤a i) ∧ ∀ i : V, SumBudget (fun j => if i ∈ j.1.sites then Poly.toll w j.1.val * p.mass (Y j) (a j) else 0) b

lemma Freight.cheaper {p : BudgetPoint} {w : V→ℝ} {Y : Address R→ Support n} {a : Address R→ℝ} {b : ℝ}
    (he : ∀ i,0<w i) {e : ℝ} (ht : 0 ≤ e) (h : Freight (later p e ht) w Y a b) : Freight p w Y a b := by
  refine ⟨h.1,h.2.1,fun i=> budget_mono' i⟩
where budget_mono' i := Push.AbsoluteSums.budget_mono (h.2.2 i) (g:=fun j => if i∈j.1.sites then Poly.toll w j.1.val*p.mass (Y j) (a j) else 0) (fun j=> by
        split; exact mul_nonneg (Poly.worth he _).le (mul_nonneg (Real.exp_pos _).le (h.2.1 _)); exact le_rfl) (fun j=> by
      split_ifs
      · apply mul_le_mul_of_nonneg_left _ (Poly.worth he _).le
        unfold BudgetPoint.mass later; apply mul_le_mul_of_nonneg_right _ (h.2.1 _); apply Real.exp_monotone
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right ht) (by positivity)
      exact le_rfl)

lemma Freight.anchor {p : BudgetPoint} {w : V→ℝ} {Y : Address R→ Support n} {a : Address R→ℝ} {b : ℝ}
    (he : ∀ i,0<w i) (h : Freight p w Y a b) (T : Hot R) :
    SumBudget (fun i=> p.mass (Y (T,i)) (a (T,i))) (b/ Poly.toll w T.val):= by
  obtain ⟨v,hv⟩:= T.property
  have hm := Push.AbsoluteSums.budget_pull (fun i: ℕ=> (T,i)) (Prod.mk_right_injective _) (h.2.2 v)
  change v ∈ T.sites at hv
  simp only [hv,↓reduceIte] at hm
  have hx := Poly.worth he T.val
  have hh:= Push.AbsoluteSums.budget_scale (inv_nonneg.mpr hx.le) hm
  simpa only [← mul_assoc,inv_mul_cancel₀ hx.ne',one_mul,div_eq_inv_mul] using hh

namespace Registers
variable {A : Registers R X G n} {p : BudgetPoint} {O : Readers V X n} {w : V→ℝ}

structure Layout (p : BudgetPoint) (O : Readers V X n) (A : Registers R X G n) : Prop where
  assigns i v : v∈i.1.sites → O.source.uses v ⊆ A.static i
  contiguous i v : v∈i.1.sites → O.source.uses v⊆A.sites i
  fixed i : Slotted i.1.sites (A.constant i)
  static i : Reads O.locus (A.static i) i.1.sites (A.constant i)
  extendsAt i U : Slotted i.1.sites (fun x=> A.body i x U)
  track i U : Reads O.locus (A.sites i) i.1.sites (fun x=> A.body i x U)
  smooth i x : p.Regular (A.sites i) (A.body i x)

structure Budget (p : BudgetPoint) (O : Readers V X n) (A : Registers R X G n) (w : V → ℝ) (c b : ℝ) : Prop where
  globalCosts : ∃ a : Address R→ℝ, Freight p w A.static a c ∧ ∀ x, UnitPage x → ∀ i, ‖A.constant i x‖ ≤ a i
  bodyCosts : ∃ a : Address R→ℝ, Freight p w A.sites a b ∧ ∀ x, UnitPage x → ∀ i v, v∈i.1.sites →
      p.supBounds (O.source.root v) (A.sites i) (A.body i x) (a i)

-- exact log in marker coefficients. Use only with accompanying Layout,
-- Budget (and positive test weight w), or explicit convergence.

def orderZero (A : Registers R X G n) (x : Cross X) (j : Hot R) := ∑' i : ℕ,A.constant (j,i) x
def supports (p : BudgetPoint) (A : Registers R X G n) (x : Cross X) (i : Address R) : Config G n→ ℂ :=
    RG.masked p.threshold (A.sites i) (A.body i x)
def ledger (p : BudgetPoint) (A : Registers R X G n) (x : Cross X) (j : Hot R) (U : Config G n):=
    A.orderZero x j + ∑' i, A.supports p x (j,i) U
def log (p : BudgetPoint) (A : Registers R X G n) (x : Cross X) (U : Config G n) : Poly R :=
    Multi.lit R fun j=> A.ledger p x j U

omit [∀ v, NormedSpace ℂ (X v)] [∀ v, NormedAddCommGroup (X v)] in
@[simp] lemma baseline (x : Cross X) (U) : (A.log p x U).part R.quiet=0 := Multi.part_lit_quiet ..
omit [∀ v, NormedSpace ℂ (X v)] [∀ v, NormedAddCommGroup (X v)] in
@[simp] lemma alive (x : Cross X) (U) (j : Hot R) : (A.log p x U).part j.val = A.ledger p x j U:= Multi.part_lit ..

lemma Layout.mask_slots (h : A.Layout p O) (i U) : Slotted i.1.sites (fun x=> A.supports p x i U):= by
  by_cases he : Healthy p.threshold (A.sites i) U
  · simp_rw [supports,masked_eq _ _ _ _ he]; exact h.extendsAt ..
  simp_rw [supports, masked_ne _ _ _ _ he]; exact Slotted.vacant
lemma Layout.mask_reads (h : A.Layout p O) (i U) : Reads O.locus (A.sites i) i.1.sites (fun x=> A.supports p x i U):= by
  by_cases he : Healthy p.threshold (A.sites i) U
  · simp_rw [supports,masked_eq _ _ _ _ he]; exact h.track i U
  simp_rw [supports,masked_ne _ _ _ _ he]; exact fun _ _ _ => rfl

variable [Fintype V] {c b : ℝ} (hw : ∀ i,0<w i) (h : A.Layout p O) (H : A.Budget p O w c b)

include hw H h
lemma glob_series (x : Cross X) (j : Hot R) : Summable (fun i:ℕ=> A.constant (j,i) x) := by
  obtain ⟨v,y,hv,rfl⟩:= Testing.normalize x
  obtain ⟨a,he,hf⟩:= H.globalCosts
  simp_rw [(h.fixed _).stretch v]
  apply Summable.const_smul
  exact Summable.of_norm ((he.anchor hw j).2.1.of_nonneg_of_le (fun i=>norm_nonneg _) fun i=> (hf _ hv _).trans (p.loMass _ _ (he.2.1 _)))

lemma dom (x : Cross X) (j : Hot R) : RG.Dominated (fun i=> A.supports p x (j,i)) := by
  obtain ⟨v,y,hv,rfl⟩:= Testing.normalize x
  obtain ⟨a,he,hf⟩:= H.bodyCosts
  let d := ‖v^j.sites.card‖
  refine ⟨fun i=>d*p.mass _ (a (j,i)), ((he.anchor hw j).2.1.mul_left d),fun i U=>?_⟩
  dsimp only; rw [(h.mask_slots (j,i) U).stretch v y, norm_smul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hh := he.2.1 (j,i); apply le_trans _ (p.loMass _ _ hh)
  obtain ⟨s,hs⟩:= j.property
  by_cases hm : Healthy p.threshold (A.sites (j,i)) U
  · rw [supports,masked_eq _ _ _ _ hm]; exact (hf _ hv (j,i) s hs).2 _ hm [] (Nat.zero_le _) (by simp)
  rw [supports,masked_ne _ _ _ _ hm,norm_zero]; exact hh

lemma complete_reads (U) : Catalogue O.locus Finset.univ (fun x=> A.log p x U) := by
  constructor <;> intro j <;> by_cases hj : j.val.Nonempty
  · let J : Hot R:= ⟨_,hj⟩; change Slotted J.sites (fun x=> (A.log p x U).part J.val); simp_rw [alive]
    unfold ledger orderZero
    exact Slotted.plus (Slotted.series _ (fun i=> h.fixed (J,i)) (fun x=> glob_series hw h H x J)) (Slotted.series _ (fun i=> h.mask_slots (J,i) U) (fun x=> (dom hw h H x J).summable U))
  · rw [show j=R.quiet from Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp hj)]; simp_rw [baseline]; exact Slotted.vacant
  · let J : Hot R:= ⟨_,hj⟩
    intro x y H
    change (A.log p x U).part J.val=(A.log p y U).part J.val
    rw [alive,alive,ledger,ledger,orderZero,orderZero]; congr 1
    · exact tsum_congr fun i=> h.static (J,i) x y (fun k hk=> O.locus.tighter k _ _ (Finset.subset_univ _) _ _ (H k hk))
    exact tsum_congr fun i=> h.mask_reads (J,i) U x y (fun k hk=> O.locus.tighter k _ _ (Finset.subset_univ _) _ _ (H k hk))
  rw [show j=R.quiet from Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp hj)]; simp_rw [baseline]; exact fun _ _ _=>rfl
end Registers
end YM.Comparison.Density
