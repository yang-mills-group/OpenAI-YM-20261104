import YM.Integration.FVA1Physical.Round2.IndependentWordBanks

/-! Turn independent-placement testing into one family of majorants chosen
before all tests, with the very same total price. Test spaces need not be
compact, finite-dimensional, or bounded in any ambient norm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Finset Set Lattice MSbar MSbar.Whisk
open scoped Classical BigOperators
variable {σ : Type} [Fintype σ] {X : Type*} [Nonempty X]

theorem word_le_total (q : ℕ) (l : List σ) (hl : l.length = q) (f : List σ → ℝ)
    (paid : ∀ t, t.length=q → 0 ≤ f t) : f l ≤ Yarn q f := by
  induction l generalizing q f with
  | nil => subst q;exact le_rfl
  | cons i tail ih =>
    subst q
    rw [List.length_cons,twilled]
    have step := ih _ rfl (fun L => f (i::L)) (fun t len => paid (i::t) (by simp [len]))
    exact step.trans (single_le_sum (s:=univ) (f:=fun h : σ => Yarn tail.length (fun L => f (h::L)))
      (fun h _ => luster tail.length (fun t len => paid (h::t) (by simp [len]))) (mem_univ i))

theorem simultaneous_word_prices (q : ℕ) (cost : List σ → X → ℝ) (weight : List σ → ℝ)
    (pos : ∀ l, 0 < weight l) (nonneg : ∀ l, l.length=q → ∀ x, 0 ≤ cost l x)
    {B : ℝ} (uniform : ∀ x : List σ → X, Yarn q (fun l => cost l (x l)*weight l) ≤ B) :
    ∃ b : List σ → ℝ, (∀ l, l.length=q → 0 ≤ b l ∧ ∀ x, cost l x ≤ b l) ∧
      Yarn q (fun l => b l*weight l) ≤ B := by
  classical
  let F := fun (l : List σ) (x : X) => cost l x*weight l
  let C := fun l => sSup (Set.range (F l))
  have point (l : List σ) (hl : l.length=q) (x : X) : F l x ≤ B :=
    (word_le_total q l hl (fun t => F t x) (fun t ht => mul_nonneg (nonneg t ht x) (pos t).le)).trans
      (uniform (fun _ => x))
  have bdd (l : List σ) (hl : l.length=q) : BddAbove (Set.range (F l)) :=
    ⟨B,fun _ ⟨x,eqn⟩ => eqn ▸ point l hl x⟩
  have lower (l : List σ) (hl : l.length=q) (x : X) : F l x ≤ C l :=
    le_csSup (bdd l hl) (Set.mem_range_self x)
  let b := fun l => C l/weight l
  refine ⟨b,?_,?_⟩
  · intro l hl
    have all : ∀ x, cost l x ≤ b l := fun x => (le_div_iff₀ (pos l)).mpr (lower l hl x)
    exact ⟨(nonneg l hl (Classical.arbitrary X)).trans (all _),all⟩
  have same (l : List σ) : b l*weight l=C l := div_mul_cancel₀ _ (pos l).ne'
  simp_rw [same]
  let count := Yarn q (fun _ : List σ => (1:ℝ))
  have count0 : 0 ≤ count := luster q (fun _ _ => zero_le_one)
  apply le_of_forall_pos_le_add
  intro ε εpos
  let δ := ε/(1+count)
  have denom : 0 < 1+count := by linarith only [count0]
  have dpos : 0 < δ := div_pos εpos denom
  have pick (l : List σ) : ∃ x : X, l.length=q → C l ≤ F l x+δ := by
    by_cases hl : l.length=q
    · by_contra! H
      have cap : C l ≤ C l-δ := csSup_le (Set.range_nonempty _) (by
        rintro v ⟨x,rfl⟩
        exact (lt_sub_iff_add_lt.mpr (H x).2).le)
      linarith only [dpos,cap]
    · exact ⟨Classical.arbitrary X,fun h => (hl h).elim⟩
  choose x hx using pick
  have fixed := uniform x
  have fees := sheen (σ:=σ) q δ (fun _ => (1:ℝ))
  simp only [mul_one] at fees
  have cover : δ*count ≤ ε := by
    exact ((mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) dpos.le).trans_eq
      (div_mul_cancel₀ ε denom.ne'))
  exact (shiny q (fun l hl => hx l hl)).trans ((pockets q _ _).trans_le
    (add_le_add fixed (fees.trans_le cover)))

end YM.Integration.FVA1Physical.Round2.Curvature
