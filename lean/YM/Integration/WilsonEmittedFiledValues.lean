import YM.Integration.WilsonEmittedLongInvoice

/-! The saved marked coefficient and its short and winding parts use the same
Wilson group field, paid modes, and numerical running-coupling transition. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonEmittedFiledValues
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene QuadraticLocal.Sunrise
open Push.Local Push.AbsoluteSums Next.Foundations WilsonEmittedCutGrouping
open WilsonEmittedLongInvoice WilsonEmittedFiledCatalogue
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {A V : Type} [Fintype A] [DecidableEq V]
variable {I X : A→Type} {Γ : Census V} {P : A→Passport n V}
variable (M : (a:A)→I a→Row (P a) Γ G (X a)) (w : A→V→ℝ) (grades : A→V→ℕ)
variable (x : (a:A)→X a) (c : A→ℝ) (ν ℓ : A→ℕ) (B : BudgetPoint)
variable {σ b K θ : A→ℝ} {p pieces depth : A→ℕ} {g : ℝ}
variable (old : ∀a,Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (pieces a) (depth a))
variable (scope : ∀a,Invoice.Supports B (K a) (B.supportExponent+2) g (σ a) (θ a))
variable (s : Γ.Mode) (v : V) (hv : v∈s.val)
variable (μ : (a:A)→I a→Prop)
abbrev Sector := Σ a:A,{i:I a // μ a i}
def member (j : Sector μ) (g:ℝ) (U:Config G n) :=
  scalar c ν g j.1 • (M j.1 j.2.val).nominal g (x j.1) U
def field (g:ℝ) (U:Config G n) := ∑' j:Sector μ,member M x c ν μ j g U

include old scope hv in
theorem quote (m : ℕ) (fit : ∀a i, μ a i→late (M a) s m i) (U : Config G n) :
    Summable (fun j:Sector μ=>member M x c ν μ j g U) ∧
    ‖field M x c ν μ g U‖ ≤ gross w c ν B s m g p pieces depth b θ := by
  let next (a:A) (i:{i:I a//μ a i}) : {i:I a//late (M a) s m i}:=⟨i.val,fit a _ i.property⟩
  let inc : Sector μ → Index M s m := Sigma.map id next
  have insert : Injective inc := injective_id.sigma_map (fun a i h hi=>Subtype.ext (congrArg (fun z:{i:I a//late (M a) s m i}=>z.val) hi))
  have total := budget_pull inc insert (WilsonEmittedLongInvoice.rough M w grades c ν B old scope s v hv m)
  have prices : SumBudget (fun j : Sector μ=>‖member M x c ν μ j g U‖) (gross w c ν B s m g p pieces depth b θ) := by
    apply budget_mono total (fun _=>norm_nonneg _)
    intro j
    have pay:=WilsonEmittedGroupWallet.full _ _ _ (old j.1) B (scope j.1) j.2.val (x j.1) U
    have e : ‖member M x c ν μ j g U‖≤crude M c ν s m (inc j) g p depth := by
      rw [member,norm_smul]
      exact mul_le_mul_of_nonneg_left pay (norm_nonneg _)
    apply e.trans
    apply le_mul_of_one_le_left ((norm_nonneg _).trans e)
    exact Real.one_le_exp (mul_nonneg (by linarith [B.exponent_pos]) (Nat.cast_nonneg _))
  exact ⟨prices.2.1.of_norm,(norm_tsum_le_tsum_norm prices.2.1).trans prices.2.2⟩

include old scope hv in
theorem recorded (m : ℕ) (fit : ∀a i, μ a i→late (M a) s m i)
    {q:ℕ} (closed : ∀a,q+ν a=ℓ a+(Launch.index Γ (grades a) s+1)) (live : 0<g)
    (U:Config G n) : field M x c ν μ g U=(g^q)⁻¹ • words M x c ℓ μ g U := by
  let z:=fun j:Sector μ=>member M x c ν μ j g U
  have sum : Summable z := (quote M w grades x c ν B old scope s v hv μ m fit U).1
  rw [field,show (∑' j:Sector μ,member M x c ν μ j g U)=∑' j,z j from rfl,sum.tsum_sigma,tsum_fintype,words,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have single := WilsonEmittedRecordedField.value (M a) (x a) (grades a)
    (WilsonEmittedFiledCatalogue.staff M w grades x B old scope a) s live.ne' (μ a)
    (fun i hi=>(fit a i hi).1) U
  have sub : (∑' i:{i:I a//μ a i},(M a i.val).nominal g (x a) U)=
      ∑' i:I a,if μ a i then (M a i).nominal g (x a) U else 0 := by
    exact tsum_subtype (s:={i:I a|μ a i}) (fun i=>(M a i).nominal g (x a) U)
  change (∑' i:{i:I a//μ a i}, scalar c ν g a • (M a i.val).nominal g (x a) U)=_
  rw [show (∑' i:{i:I a//μ a i}, scalar c ν g a • (M a i.val).nominal g (x a) U)=scalar c ν g a * (∑' i:{i:I a//μ a i},(M a i.val).nominal g (x a) U) from tsum_mul_left,sub,single]
  have he := congrArg (fun i:ℕ=>g^i) (closed a)
  simp only [pow_add] at he
  have power : g^(ν a)*(g^(Launch.index Γ (grades a) s+1))⁻¹ = (g^q)⁻¹*g^(ℓ a) := by
    field_simp [live.ne']
    convert he using 1 <;> ring
  rw [←Complex.ofReal_inv,←Complex.real_smul]
  change (c a*g^(ν a)) • ((g^(Launch.index Γ (grades a) s+1))⁻¹ • Air.sums (M a) (fun i=>(M a i).paint (x a)) (μ a) g U)=(g^q)⁻¹ • (c a • (g^(ℓ a) • Air.sums (M a) (fun i=>(M a i).paint (x a)) (μ a) g U))
  simp only [smul_smul]
  congr 1
  linear_combination (norm := ring_nf) c a * power

end YM.Integration.WilsonEmittedFiledValues
end
