import YM.Integration.WilsonCoveredOrdinaryPolynomial

/-! Each changed finite-to-cover logarithmic coefficient is charged before taking the
truncated ordinary partition product. Every old and new marker retains its own radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoveredOrdinaryWinding
open Finset Marker Multi Comparison.RG02 WilsonCoveredOrdinaryPolynomial
open WilsonIndependentOrdinaryPairGrade
open scoped Classical BigOperators
open private productMass from YM.Integration.WilsonFiniteOrdinaryTail

private theorem whole {I : Type*} (S : Finset I) (w : I → ℝ) (pos : ∀i,0 < w i)
    (p : I → Polynomial ℂ) {M : ℝ} (paid : ∀ i∈S,w i*mass (p i) ≤ M) :
    (∏ i∈S,w i) * mass (∏i∈S,p i) ≤ M^S.card := calc
  _ ≤ (∏i∈S,w i)*(∏ i∈S,mass (p i)) := mul_le_mul_of_nonneg_left
      (productMass S p) (prod_nonneg (fun i _=>(pos i).le))
  _ = ∏i∈S,(w i*mass (p i)) := (prod_mul_distrib ..).symm
  _ ≤ ∏_i∈S,M := prod_le_prod (fun i _=>mul_nonneg (pos i).le (IterationFour.Series.mass_nn _)) paid
  _ = _ := by simp

private theorem changed {I : Type*} [DecidableEq I] (S : Finset I) (w : I → ℝ) (pos : ∀i,0<w i)
    (p q : I → Polynomial ℂ) {M E : ℝ} (big : 1≤M) (ep : 0≤E)
    (both : ∀ i∈S,w i*mass (p i) ≤ M ∧ w i*mass (q i) ≤ M ∧ w i*mass (p i-q i) ≤ E) :
    (∏ i∈S,w i)*mass ((∏ i∈S,p i)-∏ i∈S,q i) ≤ (S.card:ℝ)*E*M^S.card := by
  induction S using Finset.induction_on with
  | empty => simp [mass]
  | @insert i S miss ih =>
    have sale:=both i (mem_insert_self i S)
    have rest := fun d (hd:d∈S) => both d (mem_insert_of_mem hd)
    have past:=ih rest
    have allQ:=whole S w pos q (fun d hd=>(rest d hd).2.1)
    let P:=∏d∈S,p d
    let Q:=∏d∈S,q d
    let Z:=∏d∈S,w d
    have zp:0 ≤ Z := prod_nonneg (fun d _=>(pos d).le)
    have mp:0 ≤ M := zero_le_one.trans big
    have scale : E*M^S.card ≤ (E*M^S.card)*M := le_mul_of_one_le_right (by positivity) big
    simp only [prod_insert miss,card_insert_of_notMem miss,Nat.cast_add,Nat.cast_one]
    change w i*Z*mass (p i*P-q i*Q) ≤ ((S.card:ℝ)+1)*E*M^(S.card+1)
    rw [show p i*P-q i*Q=p i*(P-Q)+(p i-q i)*Q from by ring]
    calc
      _ ≤ w i*Z*(mass (p i)*mass (P-Q)+mass (p i-q i)*mass Q) :=
        mul_le_mul_of_nonneg_left ((IterationFour.Series.mass_add ..).trans
          (add_le_add (IterationFour.Series.mass_mul ..) (IterationFour.Series.mass_mul ..)))
          (mul_nonneg (pos i).le zp)
      _ = (w i*mass (p i))*(Z*mass (P-Q))+(w i*mass (p i-q i))*(Z*mass Q) := by ring
      _ ≤ M*((S.card:ℝ)*E*M^S.card)+E*M^S.card := add_le_add
        (mul_le_mul sale.1 past (mul_nonneg zp (IterationFour.Series.mass_nn _)) mp)
        (mul_le_mul sale.2.2 allQ (mul_nonneg zp (IterationFour.Series.mass_nn _)) ep)
      _ ≤ M*((S.card:ℝ)*E*M^S.card)+(E*M^S.card)*M := add_le_add le_rfl scale
      _ = _ := by rw [pow_succ];ring

variable {V : Type} [Fintype V] [DecidableEq V] {J : Census V}

omit [Fintype V] in
theorem priced (r : ℕ) (F K : ℕ → Poly J) (z : ℂ) (hz : ‖z‖≤1) (s : J.Mode)
    (w : V → ℝ) (wp : ∀v,0<w v) (M δ : ℝ) (mp : 1≤M) (dp : 0≤δ)
    (filed : ∀d:Hot J,d.val.val⊆s.val → Poly.toll w d.val*mass (row r (fun i=>(F i).part d.val))≤M)
    (winding : ∀d:Hot J,d.val.val⊆s.val → ∀i,i≤r →
        Poly.toll w d.val*‖(F i).part d.val-(K i).part d.val‖≤δ) :
    let E:=((r:ℝ)+1)*δ
    Poly.toll w s*‖evaluated r F z s-evaluated r K z s‖ ≤
      ∑ h∈shards J s,(h.val.card:ℝ)*E*(M+E)^h.val.card := by
  intro E
  let p (d:Hot J):=row r (fun i=>(F i).part d.val)
  let q (d:Hot J):=row r (fun i=>(K i).part d.val)
  let κ (d:Hot J):=Poly.toll w d.val
  have positive (d:Hot J):0<κ d := Poly.worth wp _
  have ep:0≤E := by dsimp [E]; positivity
  have sale (d:Hot J)(hd:d.val.val⊆s.val):κ d*mass (p d-q d)≤E := by
    refine (mul_le_mul_of_nonneg_left (distance r _ _) (positive d).le).trans ?_
    rw [mul_sum]
    exact (sum_le_sum (fun i hi=>winding d hd i (Nat.le_of_lt_succ (mem_range.mp hi)))).trans_eq (by simp [E])
  have bills (d:Hot J)(hd:d.val.val⊆s.val):κ d*mass (p d)≤M+E ∧ κ d*mass (q d)≤M+E ∧ κ d*mass (p d-q d)≤E := by
    refine ⟨(filed d hd).trans (le_add_of_nonneg_right ep),?_,sale d hd⟩
    have back : q d=p d-(p d-q d) := by abel
    calc
      _ ≤ κ d*(mass (p d)+mass (p d-q d)) := mul_le_mul_of_nonneg_left
        ((congrArg mass back).le.trans (IterationFour.Series.mass_sub ..)) (positive d).le
      _ ≤ M+E := by rw [mul_add];exact add_le_add (filed d hd) (sale d hd)
  have poly : evaluated r F z s-evaluated r K z s =
      partialValue r z (ordinary r F s-ordinary r K s) := by
    simp only [evaluated,partialValue,Polynomial.coeff_sub,mul_sub,sum_sub_distrib]
  rw [poly]
  refine (mul_le_mul_of_nonneg_left (truncates r z hz _) (Poly.worth wp _).le).trans ?_
  change Poly.toll w s*mass ((∑h∈shards J s,∏d∈h.val,p d)-(∑h∈shards J s,∏d∈h.val,q d)) ≤ _
  rw [←sum_sub_distrib]
  refine (mul_le_mul_of_nonneg_left (IterationFour.Series.mass_sum ..) (Poly.worth wp _).le).trans ?_
  rw [mul_sum]
  apply sum_le_sum
  intro h hit
  rw [WilsonFiniteOrdinaryTail.toll w s h hit]
  exact changed h.val κ positive p q (mp.trans (le_add_of_nonneg_right ep)) ep
    (fun d hd=>bills d (WilsonReceivedOrdinaryFaces.contained s h hit d hd))

end YM.Integration.WilsonCoveredOrdinaryWinding
