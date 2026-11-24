import YM.Integration.WilsonIndependentOrdinaryPairGrade

/-! The signed ordinary hearing on a common original vacuum and its normalized finite Wick program. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedOrdinaryHearing
open Finset Marker Lattice Wilson RG QuadraticLocal Extra.Trajectories Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Cumulants
open FVA1Physical.Round2.CP5 WilsonIndependentOrdinaryPairGrade
open scoped Classical BigOperators

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}

theorem clear {G : Gauge} {n : Side} {P : Rep G n} {T ι : Type} {o : V → Site n}
    (A : Gallery T ι o P R) (x : T) (U : Config G n) (empty : flags P.p.threshold U=∅) :
    ((((P.eval U:ℂ)⁻¹) • A.density x U).part R.quiet) = 1 := by
  have zero : (A.E.log x U).part R.quiet=0 := by
    by_cases sums : Summable (fun j => A.E.frame j x U)
    · exact Lamps.quiet_of_hasSum x U sums
    · rw [Lamps.log,tsum_eq_zero_of_not_summable sums]
      rfl
  have vac : P.eval U = Real.exp (P.exponent U) := by
    rw [Rep.eval,P.activities.gas_one (p:=P.p) empty,mul_one]
  have positive : (Real.exp (P.exponent U):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  rw [Gallery.density,gallery_gas_one A x U empty,mul_one,Poly.part_smul,Poly.part_smul,
    Poly.pass_part _ zero,mul_one,vac,inv_mul_cancel₀ positive]

private theorem in_between (y t z : ℂ) : ‖y-z‖ ≤ ‖y-t‖+‖t-z‖ := by
  simpa only [sub_add_sub_cancel] using norm_add_le (y-t) (t-z)

private theorem restore (y t : ℂ) (e : ℝ) (h : ‖y-t‖≤e) : ‖y‖≤‖t‖+e := by
  calc
    ‖y‖ = ‖t+(y-t)‖ := by rw [add_sub_cancel]
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl h)

/-- Four signed logarithmic prices buy the full AB−C moment. Only the
two filed singleton polynomials enter its discarded total-degree terms. -/
theorem priced {r : ℕ} (Y : Poly R) (W : Grade R r) (hY : Y.part R.quiet=1)
    (unit : UnitLeading W) (sym : Symmetric W) (g : ℂ) (small : ‖g‖≤1)
    (a b c : V) (s : R.Mode) (diff : a≠b) (pair : s.val={a,b})
    (cost : R.Mode → ℝ)
    (signed : ∀ t ∈ ({s,R.fire c,R.fire a,R.fire b} : Finset R.Mode),
      ‖(logTo (Fintype.card V) Y-value g (logMarked W)).part t‖≤cost t) :
    let P := render (ratio W)
    let Z := value g (ratio W)
    let T := value g (logMarked W)
    let A := R.fire a
    let B := R.fire b
    ‖(Y.part s-Y.part (R.fire c))-(Z.part s-Z.part (R.fire c))‖ ≤
      (cost s + cost (R.fire c) + cost A*(‖T.part B‖ + cost B) + ‖T.part A‖*cost B) +
      ‖g‖^(r+1)*(mass (slot A P)*mass (slot B P)) := by
  intro P Z T A B
  let middle := T.part s-T.part (R.fire c)+T.part A*T.part B
  have first := WilsonReceivedCenteredMoment.priced Y T hY a b c s diff pair cost signed
  have last : ‖middle-(Z.part s-Z.part (R.fire c))‖ ≤ ‖g‖^(r+1)*(mass (slot A P)*mass (slot B P)) := by
    change ‖(T.part s-T.part (R.fire c)+T.part A*T.part B)-(Z.part s-Z.part (R.fire c))‖≤_
    rw [overflow W unit sym g a b c s diff pair]
    exact product_price r (slot A P) (slot B P) g small
  have hb := signed B (by change R.fire b∈_; simp)
  have ha := signed A (by change R.fire a∈_; simp)
  have ea : 0≤cost A := (norm_nonneg _).trans ha
  have byName : ‖Y.part B-T.part B‖ ≤ cost B := by
    rw [←log_to Y hY _ (fun t=>Finset.card_le_univ t.val),part_sub,lamp b Y hY] at hb
    exact hb
  have yb := restore _ _ _ byName
  apply (in_between _ middle _).trans
  refine add_le_add (first.trans ?_) last
  exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left yb ea)) le_rfl

end YM.Integration.WilsonReceivedOrdinaryHearing

