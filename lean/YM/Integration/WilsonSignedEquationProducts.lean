import YM.Integration.WilsonOffsetEquationLaw

/-! Remove every separated equation insertion only after taking the signed
product with the same exterior in the original normalized Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSignedEquationProducts
open Function Set Filter MeasureTheory Lattice Wilson RG Labels Source Push
open scoped Classical Topology BigOperators
variable {G : Gauge} {n : Side} {I : Type}

theorem erase (β : ℝ) (K : I → Set (Site n)) (A D : I → Config G n → ℂ)
    (ha : ∀ i, Continuous (A i)) (hd : ∀ i, Continuous (D i))
    (away : ∀ i j, i ≠ j → LocalOn (K i) (A j) ∧ LocalOn (K i) (D j))
    (zero : ∀ i (Z : Config G n → ℂ), LocalOn (K i) Z → Envelope Z →
        moment β (fun U => D i U * Z U) = 0) (s : Finset I)
    (X : Config G n → ℂ) (hX : Envelope X) (hK : ∀ i ∈ s, LocalOn (K i) X) :
    moment β (fun U => (∏ i ∈ s, A i U) * X U) =
      moment β (fun U => (∏ i ∈ s, (A i U-D i U)) * X U) := by
  classical
  induction s using Finset.induction_on generalizing X with
  | empty => simp only [Finset.prod_empty]
  | insert i s hi ih =>
    let Z (U : Config G n) := (∏ j ∈ s, (A j U-D j U)) * X U
    have hc : Continuous (fun U => ∏ j ∈ s, (A j U-D j U)) :=
      continuous_finsetProd _ fun j _ => (ha j).sub (hd j)
    have hZ : Envelope Z := (Mark.cont_envelope hc).mulC hX
    have zeroi := zero i Z (by
      intro U V H
      apply congrArg₂ (· * ·)
      · apply Finset.prod_congr rfl
        intro j hj
        have same := away i j (fun h => hi (h ▸ hj))
        rw [same.1 U V H,same.2 U V H]
      · exact hK i (Finset.mem_insert_self _ _) U V H) hZ
    have more := ih (fun U => A i U * X U) ((Mark.cont_envelope (ha i)).mulC hX)
      (fun j hj U V same => congrArg₂ (· * ·)
        ((away j i (fun h => hi (h ▸ hj))).1 U V same)
        (hK j (Finset.mem_insert_of_mem hj) U V same))
    have remove : moment β (fun U => A i U * Z U) =
        moment β (fun U => (A i U-D i U)*Z U) := by
      unfold moment at zeroi ⊢
      simp_rw [sub_mul]
      rw [integral_sub (Mark.times_integrable (ha i) hZ)
        (Mark.times_integrable (hd i) hZ),zeroi,sub_zero]
    simp only [Finset.prod_insert hi]
    calc
      _ = moment β (fun U => (∏ j ∈ s, A j U)*(A i U*X U)) := by
        congr 1; funext U; ring
      _ = _ := more
      _ = moment β (fun U => A i U*Z U) := by
        congr 1; funext U; unfold Z; ring
      _ = _ := remove
      _ = _ := by congr 1; funext U; unfold Z; ring

end YM.Integration.WilsonSignedEquationProducts
