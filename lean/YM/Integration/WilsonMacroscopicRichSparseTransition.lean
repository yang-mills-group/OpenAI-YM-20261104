import YM.Integration.WilsonMacroscopicRichLastResponse

/-! A local variation of the full original transition retains the positive factors on every untouched link. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichSparseTransition
open Function Filter Set MeasureTheory Lattice Wilson RG Source Next.Foundations Push.Local Push.Local.Kernel
open PhysicalNext.Repeat.Legato RGComparison.Core16
open scoped Classical BigOperators Topology
variable {G : Gauge} {c f : Side}

/-- These are the actual varied lower links. All other coordinates stay in the physical likelihood. -/
def Supported (J : Edges c) (A : Directions G c) := ∀ i, i ∉ J → A i = 0

theorem outside (S : StepData c f) (β : ℝ) (J : Edges c) (Q V : Config G c)
    (A : Directions G c) (locality : Supported J A) (t : ℝ) :
    noisy S β Jᶜ Q (increment V (t • A)) = noisy S β Jᶜ Q V := by
  apply Finset.prod_congr rfl
  intro i hi
  have zero := locality i (Finset.mem_compl.mp hi)
  have at_zero : G.lieExp 0 = 1 := G.mat_lieExp_zero
  simp only [increment,Pi.smul_apply,zero,smul_zero,at_zero,one_mul]

theorem row (S : StepData c f) (β : ℝ) (J : Edges c) (Q : Config G c)
    (l : List (Directions G c)) (ha : ∀ A∈l,Supported J A) (V : Config G c) :
    leftDerivs (noisy S β Finset.univ Q) l V = noisy S β Jᶜ Q V * leftDerivs (noisy S β J Q) l V := by
  induction l generalizing V with
  | nil =>
    change (∏ i,_) = (∏ i∈Jᶜ,_) * (∏ i∈J,_)
    rw [mul_comm,Finset.prod_mul_prod_compl]
  | cons A l ih =>
    have old : ∀ B∈l,Supported J B := fun B hB => ha B (List.mem_cons_of_mem _ hB)
    change deriv (fun t : ℝ => leftDerivs (noisy S β Finset.univ Q) l (increment V (t • A))) 0 = _
    simp_rw [ih old, outside S β J Q V A (ha A (List.mem_cons_self ..))]
    exact deriv_const_mul_field ..

theorem bound (S : StepData c f) (β : ℝ) (J : Edges c) (U : Config G f) (V : Config G c)
    (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (l : List (Directions G c)) (hk : l.length ≤ k)
    (ha : ∀ A∈l,Supported J A) (size : ∀ A∈l,∀ i∈J,‖A i‖ ≤ r) :
    ‖weights S U (fun Q => leftDerivs (noisy S β Finset.univ Q) l V)‖ ≤
      (noiseFactor G (β*S.kernel.penalty) k J.card r)^k * S.density β U V := by
  let L := noiseFactor G (β*S.kernel.penalty) k J.card r
  have one : 1 ≤ L := noiseFactor_ge G _ k J.card hr
  change ‖∑ t, S.likelihood U t * _‖ ≤ L^k * (∑ t, S.likelihood U t * S.noise β (S.prediction U t) V)
  rw [Finset.mul_sum]
  apply (norm_sum_le ..).trans (Finset.sum_le_sum ?_)
  intro t _
  let Q := S.prediction U t
  have b := noisy_bound S β J Q V hr l hk size
  have full : S.noise β Q V = noisy S β Jᶜ Q V * noisy S β J Q V :=
    row S β J Q [] (by simp) V
  have raw : ‖leftDerivs (noisy S β Finset.univ Q) l V‖ ≤ L^k * S.noise β Q V := by
    rw [full,row S β J Q l ha V,norm_mul,Real.norm_of_nonneg (noisy_pos S β Jᶜ Q V).le]
    calc _ ≤ noisy S β Jᶜ Q V * (L^k * noisy S β J Q V) :=
          mul_le_mul_of_nonneg_left (b.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one hk) (noisy_pos S β J Q V).le)) (noisy_pos S β Jᶜ Q V).le
         _ = _ := by ring
  rw [norm_mul,Real.norm_of_nonneg (S.likelihood_pos ..),mul_left_comm]
  exact mul_le_mul_of_nonneg_left raw (S.likelihood_pos ..)

end YM.Integration.WilsonMacroscopicRichSparseTransition
