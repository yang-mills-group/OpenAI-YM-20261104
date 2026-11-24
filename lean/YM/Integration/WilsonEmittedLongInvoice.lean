import YM.Integration.WilsonEmittedCompactBalance
import YM.Push.LOCAL_SPLITTING.Budget

/-! Each long or winding original word keeps its own true support and its
own measured-order obligation in the signed lower transfer. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonEmittedLongInvoice
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Push.Local Push.AbsoluteSums Next.Foundations Comparison.Density
open WilsonEmittedCutGrouping WilsonEmittedGroupWallet
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {A V : Type} [Fintype A] [DecidableEq V]
variable {I X : A→Type} {Γ : Census V} {P : A→Passport n V}
variable (M : (a:A)→I a→Row (P a) Γ G (X a)) (w : A→V→ℝ) (grades : A→V→ℕ)
variable (x : (a:A)→X a) (c : A→ℝ) (ν : A→ℕ) (B : BudgetPoint)
variable {σ b K θ : A→ℝ} {p pieces depth : A→ℕ} {g : ℝ}
variable (old : ∀a,Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (pieces a) (depth a))
variable (scope : ∀a,Invoice.Supports B (K a) (B.supportExponent+2) g (σ a) (θ a))
variable (s : Γ.Mode) (v : V) (hv : v∈s.val) (m : ℕ) {o : Site n}
abbrev Index := Σ a:A,{i:I a // late (M a) s m i}
def scalar (g : ℝ) (a:A) : ℂ := (c a * g^(ν a):ℝ)
variable (h : Index M s m)
def ground := (M h.1 h.2.val).ground B
def burst (g:ℝ) := (scalar c ν g h.1) • (M h.1 h.2.val).nominal g (x h.1)
def pay (g:ℝ) := ‖scalar c ν g h.1‖ * (M h.1 h.2.val).charge B g
def crude (g:ℝ) (p depth : A→ℕ) :=
  ‖scalar c ν g h.1‖ * (ceiling g (p h.1) (depth h.1) * (M h.1 h.2.val).salary)
def budget (g:ℝ) (p pieces depth : A→ℕ) (K b θ : A→ℝ) :=
  ∑a:A,‖scalar c ν g a‖ * ((Poly.toll (w a) s)⁻¹*
      (Invoice.price B (K a) (p a+depth a+1) (pieces a) (B.supportExponent+2) (θ a) G*b a*Real.exp (-(θ a))^m))
def gross (g:ℝ) (p pieces depth : A→ℕ) (b θ : A→ℝ) :=
  ∑a:A,‖scalar c ν g a‖ * (ceiling g (p a) (depth a)*((Poly.toll (w a) s)⁻¹*
      stock B (p a+depth a+1) (pieces a) m (b a) (θ a)))
local notation "κ" => Index M s m
omit [Fintype A] in
include old scope hv in
theorem terms (home : ∀a,(P a).origin v=o) (z:κ) :
    o∈ground M B s m z ∧ B.Regular (ground M B s m z) (burst M x c ν s m z g) ∧
    B.supBounds o (ground M B s m z) (burst M x c ν s m z g) (pay M c ν B s m z g) ∧
    ∀ U, ‖burst M x c ν s m z g U‖≤crude M c ν s m z g p depth := by
  let T:=M z.1 z.2.val
  have own : o∈T.ground B := home z.1 ▸ T.heard B.B v (z.2.property.1 ▸ hv) ((P z.1).born v)
  refine ⟨own,regular_smul _ (T.legal B g (x z.1)),
    bound_smul _ (T.supported B g (x z.1) o ((old z.1).honor z.2.val) own),?_⟩
  intro U
  rw [burst,Pi.smul_apply,norm_smul]
  exact mul_le_mul_of_nonneg_left (WilsonEmittedGroupWallet.full _ _ _ (old z.1) B
    (scope z.1) z.2.val (x z.1) U) (norm_nonneg _)

private theorem combine {f : κ→ℝ} {D : A→ℝ}
    (h : ∀a,SumBudget (fun i=>f ⟨a,i⟩) (D a)) : SumBudget f (∑ a,D a) := by
  apply sumBudget_sigma h
  exact ⟨fun a=>(tsum_nonneg (h a).1).trans (h a).2.2, (hasSum_fintype _).summable,by rw [tsum_fintype]⟩

include old scope hv in
theorem regular :
    SumBudget (fun z:κ=>reservedMass B (ground M B s m z) (pay M c ν B s m z g))
      (budget (G:=G) w c ν B s m g p pieces depth K b θ) := by
  apply combine
  intro a
  have h:=budget_scale (norm_nonneg (scalar c ν g a))
    (WilsonEmittedGroupWallet.regular (M a) (w a) (grades a) (old a) B (scope a) m s v hv)
  convert h using 1
  ext i
  dsimp only [reservedMass,ground,pay]
  ring

include old scope hv in
theorem rough :
    SumBudget (fun z:κ=>reservedMass B (ground M B s m z) (crude M c ν s m z g p depth))
      (gross w c ν B s m g p pieces depth b θ) := by
  apply combine
  intro a
  have h:=budget_scale (norm_nonneg (scalar c ν g a))
    (WilsonEmittedGroupWallet.rough (M a) (w a) (grades a) (old a) B (scope a) m s v hv)
  convert h using 1
  ext i
  dsimp only [reservedMass,ground,crude]
  ring

end YM.Integration.WilsonEmittedLongInvoice
end
