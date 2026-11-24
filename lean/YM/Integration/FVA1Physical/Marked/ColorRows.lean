import YM.Integration.FVA1Physical.Marked.ComplexChannels
import YM.Integration.FVA1Physical.TestedBudget
import YM.Next.FOUNDATIONS.Regular

/-! Polarize the actual represented rows without any cost in spatial
volume. Halving each source radius pays every polarization of that slot,
including the full factorial sum of true ordered regular derivatives. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Marker LocalComparison RG3.Script.Picnic Push.AbsoluteSums
open scoped Classical BigOperators
variable {I : Type} [DecidableEq I] {B : Census I} {G : Gauge} {n : Side}

def blend {E : Type*} [AddCommMonoid E] [Module ℂ E] (s : Finset I) (F : Finset I→E) : E :=
  ∑ t∈s.powerset, (Complex.I ^ t.card) • F t

def copies (s : Finset I) : ℝ := s.powerset.card

omit [DecidableEq I] in
theorem norm_blend {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E] (s : Finset I)
    (F : Finset I→E) {C : ℝ} (bound : ∀ t∈s.powerset, ‖F t‖ ≤ C) : ‖blend s F‖ ≤ copies s * C := by
  calc
    _ ≤ ∑ t∈s.powerset, ‖(Complex.I^t.card) • F t‖ := norm_sum_le ..
    _ ≤ ∑ _∈s.powerset,C := Finset.sum_le_sum fun t ht=>by simpa only [norm_smul,norm_pow,Complex.norm_I,one_pow,one_mul] using bound t ht
    _ = _ := by simp [copies]

theorem half_toll (w : I→ℝ) (s : B.Mode) :
    Poly.toll (fun j=>w j/2) s * copies s.val = Poly.toll w s := by
  unfold Poly.toll copies
  rw [Finset.prod_div_distrib,Finset.card_powerset]
  push_cast
  simp

omit [DecidableEq I] in
theorem blend_eval {A : Type*} (s : Finset I) (F : Finset I→A→ℂ) (v : A) :
    blend s F v = blend s (fun t=>F t v) := by simp only [blend,Finset.sum_apply,Pi.smul_apply]

private theorem jet_scale (a : ℂ) (f : Config G n→ℂ) (l : List (Directions G n)) (u : Config G n) :
    leftDerivs (a • f) l u = a • leftDerivs f l u := by
  induction l generalizing u with
  | nil => rfl
  | cons A l ih => simp only [leftDerivs,ih]; exact deriv_fun_const_smul_field ..

omit [DecidableEq I] in
theorem regular_blend {p : BudgetPoint} {S : Support n} (s : Finset I) (F : Finset I → Config G n→ℂ)
    (h : ∀ t∈s.powerset, p.Regular S (F t)) : p.Regular S (blend s F) := by
  classical
  unfold blend
  apply Finset.sum_induction _ (p.Regular S)
  · exact fun _ _=>Next.Foundations.regular_add
  · exact Push.Local.regular_const 0
  intro t ht
  exact Next.Foundations.regular_smul _ (h t ht)

omit [DecidableEq I] in
theorem blend_grain {p : BudgetPoint} {S : Support n} (s : Finset I) (F : Finset I → Config G n→ℂ)
    (o : Site n) (C : ℝ) (regular : ∀ t, p.Regular S (F t))
    (price : ∀ t, Mix.grain p S (F t) o C) : Mix.grain p S (blend s F) o (copies s*C) := by
  choose beta nonneg total controls using price
  refine ⟨fun j=>∑ t∈s.powerset,beta t j,fun _=>Finset.sum_nonneg (fun _ _=>nonneg ..),?_,?_⟩
  · simp_rw [Finset.sum_div]
    rw [Finset.sum_comm]
    exact (Finset.sum_le_sum (fun t _=>total t)).trans_eq (by simp [copies])
  intro l hl ha u hu
  rw [blend,Push.Local.left_sum _ _ _ _ (fun t _=>(Next.Foundations.regular_smul (Complex.I^t.card) (regular t)).smooth u hu) hl]
  apply (norm_sum_le ..).trans
  exact Finset.sum_le_sum (fun t _=>by simpa only [jet_scale,norm_smul,norm_pow,Complex.norm_I,one_pow,one_mul] using controls t l hl ha u hu)

variable {o : I→Site n} {P : Rep G n}

/-- The common represented layout with complex-channel coefficients restored
on the original marker, including the marked forced kernels. -/
def colorTaste (T : Taste (Finset I) o P B) : Taste Unit o P B where
  menu := {
    origins := T.menu.origins, rays := T.menu.rays, branch := T.menu.branch, marks := T.menu.marks
    global := fun _ v=>blend {v} (fun t=>T.menu.global t v)
    regular := fun _ i=>blend (T.menu.rays i).val (fun t=>T.menu.regular t i)
    force := fun _ i j=>blend (T.menu.marks i j).val (fun t=>T.menu.force t i j) }
  root := T.root
  tag := T.tag
  site := T.site
  score := fun _ i=>blend (T.tag i).val (fun t=>T.score t i)

end YM.Integration.FVA1Physical.Marked
