import YM.Integration.WilsonEmittedFiledValues

/-! The first row collects the short signed polynomial on its common
healthy cube. A different row retains each actual long path and its hard
owner. Their sum on every field is the whole original dated coefficient. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonEmittedSparseRows
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene QuadraticLocal.Sunrise
open Push.Local Push.AbsoluteSums Next.Foundations Comparison.Density.Mirrors
open WilsonEmittedCutGrouping WilsonEmittedFiledCatalogue
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {A V : Type} [Fintype A] [DecidableEq V]
variable {I X : A→Type} {Γ : Census V} {P : A→Passport n V}
variable (M : (a:A)→I a→Row (P a) Γ G (X a)) (w : A→V→ℝ) (grades : A→V→ℕ)
variable (x : (a:A)→X a) (c : A→ℝ) (ν ℓ : A→ℕ) (B : BudgetPoint)
variable {σ b K θ : A→ℝ} {p pieces depth : A→ℕ} {g : ℝ}
variable (old : ∀a,Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (pieces a) (depth a))
variable (scope : ∀a,Invoice.Supports B (K a) (B.supportExponent+2) g (σ a) (θ a))
variable (s : Γ.Mode) (v : V) (hv : v∈s.val) {o : Site n} (m D q : ℕ)
local notation "near" => (fun a=>early (M a) s m)
local notation "far" => (fun a=>late (M a) s m)
abbrev Key := Unit ⊕ WilsonEmittedLongInvoice.Index M s m
def chart (g:ℝ) := (↑((g^q)⁻¹):ℂ) • words M x c ℓ near g
def site (o:Site n) : Key M s m → Support n :=
  Sum.elim (fun _=>neighborhood D o) (WilsonEmittedLongInvoice.ground M B s m)
def value (g:ℝ) : Key M s m → Config G n→ℂ :=
  Sum.elim (fun _=>chart M x c ℓ s m q g) (fun z=>WilsonEmittedLongInvoice.burst M x c ν s m z g)
def soft (g scale:ℝ) : Key M s m→ℝ :=
  Sum.elim (fun _=>‖(↑((g^q)⁻¹):ℂ)‖*scale) (fun z=>WilsonEmittedLongInvoice.pay M c ν B s m z g)
local notation "cash" a:max => WilsonEmittedLongInvoice.gross w c ν B s a g p pieces depth b θ
local notation "rent" a:max => WilsonEmittedLongInvoice.budget (G:=G) w c ν B s a g p pieces depth K b θ
def large (g:ℝ) (p pieces depth:A→ℕ) (b θ:A→ℝ) : Key M s m→ℝ :=
  Sum.elim (fun _=>WilsonEmittedLongInvoice.gross w c ν B s 0 g p pieces depth b θ)
    (fun z=>WilsonEmittedLongInvoice.crude M c ν s m z g p depth)

private theorem joint {Z:Type} (f:Unit⊕Z→ℝ) {e : ℝ}
    (h₀ : 0≤f (.inl ())) (h : SumBudget (fun z=>f (.inr z)) e) : SumBudget f (f (.inl ())+e) := by
  have hh : HasSum f (f (.inl ())+∑'z:Z,f (.inr z)) :=
    HasSum.sum (f:=f) (by change HasSum (fun a:Unit=>f (.inl a)) _; simpa only [Fintype.sum_unique] using (hasSum_fintype (fun a:Unit=>f (.inl a)))) h.2.1.hasSum
  refine ⟨?_,hh.summable,hh.tsum_eq.trans_le (add_le_add_right h.2.2 _)⟩
  intro z
  rcases z with x|x
  · exact h₀
  · exact h.1 x

include scope old hv in
theorem original (home : ∀a,(P a).origin v=o) (fixed : o∈neighborhood D o)
    (live : 0<g) (closed : ∀a,q+ν a=ℓ a+(Launch.index Γ (grades a) s+1))
    {scale : ℝ} (good : B.Regular (neighborhood D o) (words M x c ℓ near g))
    (measured : B.supBounds o (neighborhood D o) (words M x c ℓ near g) scale)
    (scale0 : 0 ≤ scale) (posted : ∀ a (U:Config G n),Summable (fun i=>Spill.raw (M a) g (x a) i U)) :
    (∀z:Key M s m,o∈site M B s m D o z ∧ B.Regular (site M B s m D o z) (value M x c ν ℓ s m q g z) ∧
      B.supBounds o (site M B s m D o z) (value M x c ν ℓ s m q g z) (soft M c ν B s m q g scale z) ∧
      ∀U,‖value M x c ν ℓ s m q g z U‖≤large M w c ν B s m g p pieces depth b θ z) ∧
    SumBudget (fun z=>reservedMass B (site M B s m D o z) (soft M c ν B s m q g scale z))
      (reservedMass B (neighborhood D o) (‖(↑((g^q)⁻¹):ℂ)‖*scale)+rent m) ∧
    SumBudget (fun z=>reservedMass B (site M B s m D o z) (large M w c ν B s m g p pieces depth b θ z))
      (reservedMass B (neighborhood D o) (cash 0)+cash m) ∧
    ∀U:Config G n,(∑'z:Key M s m,value M x c ν ℓ s m q g z U)=
        ∑a:A,c a • (g^(ν a) • (Spill.Foundry.uncut (M a) g (x a) U).part s) := by
  have short (U:Config G n) := WilsonEmittedFiledValues.quote M w grades x c ν B old scope s v hv near 0
    (fun _ _ hi=>⟨hi.1,Nat.zero_le _⟩) U
  have short_read (U:Config G n) := WilsonEmittedFiledValues.recorded M w grades x c ν ℓ B old scope s v hv near 0
    (fun _ _ hi=>⟨hi.1,Nat.zero_le _⟩) closed live U
  have returned (U:Config G n) := WilsonEmittedFiledValues.quote M w grades x c ν B old scope s v hv far m
    (fun _ _=>id) U
  have long_read (U:Config G n) := WilsonEmittedFiledValues.recorded M w grades x c ν ℓ B old scope s v hv far m
    (fun _ _=>id) closed live U
  refine ⟨?_,?_,?_,?_⟩
  · intro z
    rcases z with z|z
    · refine ⟨fixed,regular_smul _ good,bound_smul _ measured,?_⟩
      intro U
      change ‖(↑((g^q)⁻¹):ℂ) • words M x c ℓ near g U‖≤cash 0
      rw [Complex.coe_smul,←short_read U]
      exact (short U).2
    · exact WilsonEmittedLongInvoice.terms M w grades x c ν B old scope s v hv m home z
  · apply joint
    · apply mul_nonneg (Real.exp_pos _).le (mul_nonneg (norm_nonneg _) scale0)
    · exact WilsonEmittedLongInvoice.regular M w grades c ν B old scope s v hv m
  · apply joint
    · exact mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans (short 1).2)
    · exact WilsonEmittedLongInvoice.rough M w grades c ν B old scope s v hv m
  · intro U
    have sum : HasSum (fun z:Key M s m=>value M x c ν ℓ s m q g z U)
        (chart M x c ℓ s m q g U+WilsonEmittedFiledValues.field M x c ν far g U) :=
      HasSum.sum (by change HasSum (fun _:Unit=>chart M x c ℓ s m q g U) _; simpa only [Fintype.sum_unique] using (hasSum_fintype (fun _:Unit=>chart M x c ℓ s m q g U))) (returned U).1.hasSum
    rw [sum.tsum_eq,chart,Pi.smul_apply,Complex.coe_smul,long_read U,←smul_add]
    rw [←WilsonEmittedFiledCatalogue.numerical M w grades x c ℓ B old scope s closed live U (fun a=>posted a U)]
    congr 1
    rw [words,words,words,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [WilsonEmittedCutGrouping.divided (M a) _ _ (WilsonEmittedFiledCatalogue.staff M w grades x B old scope a)
      s m g U]
    simp only [smul_add]

end YM.Integration.WilsonEmittedSparseRows
end
