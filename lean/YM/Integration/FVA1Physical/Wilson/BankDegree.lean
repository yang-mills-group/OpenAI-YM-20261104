import YM.Integration.FVA1Physical.Wilson.InputPrefix
import YM.Integration.FVA1Physical.Wilson.EmittedDegree

/-! The full degree of a normalized conditional observable is bounded by the
orders of the input actually used. The Gaussian tag does not create an
extra regularity condition on the physical action. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Cacao MSbar.Mosaic MSbar.Rolling MSbar.Lis MSbar.Bakery.Film MSbar.Midpoint MSbar.Heath
open Push.Uniform
open scoped Classical Topology BigOperators
variable {G:Gauge}

/-- Full degree bound in the *actual* joint coordinates after division by
the physical formal vacuum. -/
theorem normalized_input_degree (A:Issue G) (χ:ChartRatio G)
    (src:PowerSeries (Pot (Joint A.F G))) (p m:ℕ) (hm:1 ≤ m)
    (kind:Kind A.T) (pd:(mold A.pre A.F A.v).PosDef) (profile:Expanse A.T 1 p)
    (input:∀ i ≤ p,(PowerSeries.coeff i src).totalDegree ≤ m) {i:ℕ} (hi:i ≤ p) :
    (PowerSeries.coeff i (normalizedRows A χ src p)).totalDegree ≤ m*(p+1+p)+2 := by
  let d:=p+1+p
  let Q:=barbed A.F A.v χ A.T
  have ok:Kind Q:=well A.F A.v χ A.T kind
  have qcrop:Kind (cropAction p Q):=by
    unfold Kind at ok ⊢
    simpa only [cropAction,PowerSeries.coeff_mk,zero_le,if_true] using ok
  have eqn:Lap p (normalizedRows A χ src p) (growP (cropAction p Q) (cropAction p src) (fullCov A) (p+1)):=by
    apply grow_prefix (straight A.F G) pd.inv ok qcrop _ _ (Nat.lt_succ_self p) (Nat.lt_succ_self p)
    · intro j hj;simp only [cropAction,PowerSeries.coeff_mk,if_pos hj]
    · intro j hj;simp only [cropAction,PowerSeries.coeff_mk,if_pos hj]
  have slope:Expanse (cropAction p Q) m d:=by
    constructor
    intro j _
    by_cases hj:j ≤ p
    · simp only [cropAction,PowerSeries.coeff_mk,if_pos hj]
      have f:=(MSbar.Parma.expanseB A.F A.v χ p A.T profile).profile j hj
      simp only [one_mul] at f
      exact f.trans (Nat.add_le_add_right (le_mul_of_one_le_left (Nat.zero_le _) hm) 2)
    simp [cropAction,hj]
  rw [eqn i hi]
  apply outgoing_degree p m _ _ _ qcrop slope _ i hi
  intro j _
  by_cases hj:j ≤ p
  · simpa only [cropAction,PowerSeries.coeff_mk,if_pos hj] using input j hj
  simp [cropAction,hj]

end YM.Integration.FVA1Physical.Wilson
