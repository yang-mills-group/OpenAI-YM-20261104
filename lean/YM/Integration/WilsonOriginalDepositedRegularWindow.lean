import YM.Integration.WilsonOriginalDepositedRegular

/-! The incoming physical compact part pays the enlarged width. The complementary smooth part keeps its exponential tail. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalDepositedRegularWindow
open Function Finset Lattice Wilson RG Source Marker Overlay QuadraticLocal QuadraticLocal.Affinity
open WilsonOriginalDepositedRegular WilsonRetainedMarkedInletRegular
open scoped Topology Classical BigOperators
variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d} {A : Hol G}
  {P : Rep G n} {V T : Type} [DecidableEq V] {J : Census V} {o : V → Site n}
  (j : V) (q : Coefficient F n) (law : q.Format (o j) A P) (t : T → ℂ)
  (D : ℕ)

def small (P : Rep G n) (q : Coefficient F n) (D i : ℕ) : Prop := coverNumber P.p.B (q.support i) ≤ D

variable [Fintype V] (w : V → ℝ) (hw : ∀ v, 0<w v) (test : ∀ x, ‖t x‖≤1)
  {κ B : ℝ} (actual : q.remBound (o j) P κ B)
include hw test actual

theorem short :
    (lamps (J:=J) j q law t (small P q D)).Paid w P.p.B (P.p.supportExponent+2)
        (Real.exp (3*D)*cost P.p*(w j*B)) := by
  apply paid j q law t _ w hw test actual (Real.exp_nonneg _) _
  intro i hi
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have cover : (coverNumber P.p.B (q.support i) : ℝ) ≤ D := by exact_mod_cast hi
  linarith

theorem long (s : 1 ≤ P.p.supportExponent) :
    (lamps (J:=J) j q law t (fun i => ¬small P q D i)).Paid w P.p.B 0
        (Real.exp (-(P.p.supportExponent-1)*D)*cost P.p*(w j*B)) := by
  apply paid j q law t _ w hw test actual (Real.exp_nonneg _) _
  intro i hi
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h : D ≤ coverNumber P.p.B (q.support i) := Nat.le_of_lt (lt_of_not_ge hi)
  have cover : (D : ℝ) ≤ (coverNumber P.p.B (q.support i) : ℝ) := by exact_mod_cast h
  nlinarith [mul_nonneg (sub_nonneg.mpr s) (sub_nonneg.mpr cover)]

theorem whole (s : 1 ≤ P.p.supportExponent) (x : T) (U : Config G n) :
    ((lamps (J:=J) j q law t (small P q D)).log x U).part (J.fire j) +
    ((lamps (J:=J) j q law t (fun i => ¬small P q D i)).log x U).part (J.fire j) =
        t x*∑'i,q.maskedTerm P i U := by
  have hi := (short (J:=J) j q law t D w hw test actual).sums (by linarith) hw x U
  have ho := (long (J:=J) j q law t D w hw test actual s).sums (le_refl 0) hw x U
  rw [←Poly.part_plus,Lamps.log,Lamps.log,←hi.tsum_add ho,Poly.share (hi.add ho),←tsum_mul_left]
  apply tsum_congr
  intro i
  rw [Poly.part_plus,row,row]
  by_cases h : small P q D i <;> simp [h]

section
variable {Y : V → Type} [∀i, AddCommGroup (Y i)]
  {𝕜 : Type} [RCLike 𝕜] [NormedAlgebra 𝕜 ℂ] [∀i, Module 𝕜 (Y i)]
  (C : ∀i, Set (Y i)) (K : ∀i, Submodule 𝕜 (Y i)) (a : Wallet C → ℂ)

omit hw test actual [Fintype V] in
theorem taut (keep : ℕ → Prop) (h : Attn K C {j} a) :
    Taut (fun v=>{o v}) C K (lamps (J:=J) j q law a keep) := by
  constructor
  · intro i v hv
    have eq : v=j := mem_singleton.mp hv
    subst v
    exact Finset.singleton_subset_iff.mpr (law.origin i)
  · intro i U
    change Attn K C {j} (fun x => (if keep i then a x else 0)*q.regular i U)
    by_cases take : keep i
    · simp only [if_pos take]
      simpa using h.bind (Attn.solid (K:=K) (A:=C) (q.regular i U)) (show Disjoint ({j} : Finset V) ∅ by simp)
    · simp only [if_neg take,zero_mul]
      exact Attn.silent
end

end YM.Integration.WilsonOriginalDepositedRegularWindow
