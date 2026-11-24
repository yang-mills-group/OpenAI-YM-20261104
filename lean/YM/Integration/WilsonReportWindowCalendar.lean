import YM.Integration.WilsonReportWindowEnvelope

/-! Uniform authentic stage prices for a finite list of independently graded
deposited columns, in the current physical coupling before every cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportWindowCalendar
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table
open Next.Rank Extra.Multi OPE OPE.Orbits PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection WilsonReportWindowEnvelope
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G}

private theorem fitted {c u g : ℝ} (e P : ℕ) (hp : e≤P) (two : 2≤P)
    (c0 : 0≤c) (u0 : 0≤u) (gp : 0<g) (g1 : g≤1) (truePrice : c*g^2≤2) :
    (5*c+u*((g/2)⁻¹)^e)*g^P ≤ 10+u*2^e := by
  have h := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one gp.le g1 two) c0
  have e0 := pow_nonneg (inv_nonneg.mpr (half_pos gp).le) e
  have recover : ((g/2)⁻¹)^e*g^e=2^e := by
    rw [←mul_pow,show (g/2)⁻¹*g=2 by field_simp]
  have fee := (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one gp.le g1 hp) e0).trans_eq recover
  nlinarith only [h.trans truePrice,mul_le_mul_of_nonneg_left fee u0]

theorem original (hG : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (funding : FundedOriginalProperties.{u} hG δ W) (subsidy : WilsonReportColumnSubsidy.Eligible R.kit)
    {n : ℕ} (d : Fin n→ℕ) :
    ∃ (P : ℕ) (M : ℝ),1≤M ∧ ∀ᶠ k : ℕ in atTop, ∀ N p : ℕ,k≤N →
      let C := R.family; let g := regulatorRun C N p k
      0<g ∧ g≤1 ∧ C.path.levels.clock.hatBeta k*g^2≤2 ∧ ∀ j,
        units C (d j) k N p*g^P≤M := by
  obtain ⟨_,book⟩ := WilsonReportCitizenRun.on_run hG W funding subsidy
  let C := R.family
  let e (j : Fin n) := BasisCost.slots (C.labels.level (d j))
  let fee (j : Fin n) := BasisCost.price (C.localSection (d j))*(2:ℝ)^(e j)
  let P := 2+∑ j,e j
  let M := 10+∑ j,fee j
  have nonneg (j : Fin n) : 0≤fee j := mul_nonneg (zero_le_one.trans (BasisCost.price_pos _)) (by positivity)
  refine ⟨P,M,?_,?_⟩
  · dsimp only [M]
    linarith only [sum_nonneg (s:=univ) (fun j _=>nonneg j)]
  filter_upwards [(Station.hat_rate C.path.levels hG).eventually_ge_atTop (2:ℝ)] with k hot N p cut
  let β := C.path.levels.clock.hatBeta k
  let b := C.path.β N p k
  let g := regulatorRun C N p k
  have lower : β/2≤b := (R.makes.wilson.represents N p k cut).band.1
  change 2≤β at hot
  have b1 : 1≤b := by linarith only [hot,lower]
  have bp := zero_lt_one.trans_le b1
  have gp : 0<g := RG16.Literal.g_pos R.makes cut
  have eq : b*g^2=1 := by
    change b*(Real.sqrt b)⁻¹^2=1
    rw [inv_pow,Real.sq_sqrt bp.le,mul_inv_cancel₀ bp.ne']
  have g1 : g≤1 := by nlinarith only [le_mul_of_one_le_left (sq_nonneg g) b1,eq,gp]
  have scaled : β*g^2≤2 := by
    nlinarith only [eq,mul_le_mul_of_nonneg_right lower (sq_nonneg g)]
  dsimp only
  refine ⟨gp,g1,scaled,?_⟩
  intro j
  let u := BasisCost.price (C.localSection (d j))
  let c := (C.path.levels.params k).columns
  have u0 : 0≤u := zero_le_one.trans (BasisCost.price_pos _)
  have c0 : 0≤c := zero_le_one.trans (C.path.levels.params k).columns_ge
  have mass : c*g^2≤2 := (mul_le_mul_of_nonneg_right (book.money.present k) (sq_nonneg g)).trans scaled
  have je : e j≤P := (single_le_sum (f:=e) (fun _ _=>Nat.zero_le _) (mem_univ j)).trans (Nat.le_add_left ..)
  have charge (j : Fin n) : fee j≤∑i,fee i := single_le_sum (f:=fee) (fun i _=>nonneg i) (mem_univ j)
  exact (fitted (e j) P je (Nat.le_add_right ..) c0 u0 gp g1 mass).trans (add_le_add_right (charge j) 10)

end YM.Integration.WilsonReportWindowCalendar
end

