import YM.Integration.WilsonReceivedCompactQUnitTerminal

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedQUpperSoft
open Function MeasureTheory Lattice Wilson RG Labels Source Extra.Histories FVA1
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit WheelP QuadraticLocal QuadraticLocal.Advent
open Trace.Physical Trace.Physical.Germ RG16
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open WilsonReceivedGeometricCellReadout WilsonOriginalNullCorridor WilsonOriginalNullFiledStep
open XSpace XSpace.Rose OPE.Orbits
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
variable {O:Type} [Fintype O]
variable {G:Gauge} (R:Run G) {N per m k:ℕ} (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin)
  (Ψ:∀i,RG.Rep G (R.family.side i per)) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
variable (test:Test 3) (χ:Points 3 → O) (t:ℕ) (fees:Fares)
  (y:Site (R.family.side t per)) (v:O → Values (Config G (R.family.side t per)))
local notation "w" => WilsonSeparatedOriginalThermometerCells.weight test χ
local notation "mass" => (∫x:Points 3,‖test x‖)
local notation "B₀" => max fees.regular fees.primary
local notation "F₀" => R.family.labels.level 0
local notation "S₀" => R.family.localSection 0


def row (U:Config G (R.family.side t per)) := test.applyTo (fun x=>(v (χ x)).withdrawn U-
  ((Ψ t).eval U:ℂ)*(v (χ x)).filed U)

def forced (h:∀o:O,w o≠0 → Coefficient (F₀) (R.family.side t per)) (U:Config G (R.family.side t per)) :=
  test.applyTo (fun x=>if p:w (χ x)≠0 then WilsonMeasuredCoefficientTransport.account (h (χ x) p) (Ψ t) U else 0)

def named (U:Config G (R.family.side t per)) := test.applyTo (fun x=>(v (χ x)).withdrawn U)/((Ψ t).eval U:ℂ)-
  test.applyTo (fun x=>(v (χ x)).covered U)

include course in
theorem original [MeasurableSpace O] [MeasurableSingletonClass O] (simple:G.Simple) (measured:Measurable χ)
    (h:∀o:O,w o≠0 → Coefficient (F₀) (R.family.side t per)) (bought:∀o p,Paid (N:=N) R (Ψ t) fees y (v o) (h o p))
    (start:m ≤ t) (live:t ≤ N) :
    Integrable (row R Ψ test χ t v) (prior G _) ∧ Integrable (forced R Ψ test χ t h) (prior G _) ∧
    ∀U,‖((Ψ t).eval U)⁻¹ • (row R Ψ test χ t v U-forced R Ψ test χ t h U)‖ ≤ mass*(|fees.primary|+|fees.regular|) := by
  let W:=Ψ t
  let d (o:O) (U:Config G (R.family.side t per)):=if p:w o≠0 then (h o p).density y (S₀) W U else 0
  let K (o:O) (U:Config G (R.family.side t per)):=if p:w o≠0 then WilsonMeasuredCoefficientTransport.account (h o p) W U else 0
  let soft:=fun o U=>(W.eval U)⁻¹ • (d o U-K o U)
  have D:row R Ψ test χ t v=(fun U=>∑o,w o*d o U):=by
    funext U
    unfold row
    rw [WilsonSeparatedOriginalThermometerCells.tested test χ measured (fun o=>(v o).withdrawn U-((Ψ t).eval U:ℂ)*(v o).filed U)]
    apply Finset.sum_congr rfl
    intro o _
    by_cases p:w o≠0
    · rw [show d o U=(h o p).density y (S₀) W U by simp [d,p],(bought o p).2.2.2.1 U]
    · simp only [not_not] at p
      rw [p,zero_mul,zero_mul]
  have F:forced R Ψ test χ t h=(fun U=>∑o,w o*K o U):=by
    funext U
    exact WilsonSeparatedOriginalThermometerCells.tested test χ measured (fun o=>K o U)
  have ep:0 ≤ |fees.primary|+|fees.regular|:=add_nonneg (abs_nonneg _) (abs_nonneg _)
  have bill (o:O):Integrable (d o) (prior G _) ∧ Integrable (K o) (prior G _) ∧
      ∀U,‖soft o U‖ ≤ |fees.primary|+|fees.regular| := by
    by_cases p:w o≠0
    · have sale:=bought o p
      have fee:=WilsonMeasuredSignedEnvelope.original R simple π Γ Ψ course start live y (h o p) sale.1 sale.2.1
        ((h o p).density y (S₀) W) (fun _=>0) (fun _=>by simp [W])
      have stock:=(course.1.walk t start live).truep
      simp only [d,K,soft,dif_pos p]
      refine ⟨((h o p).envelope (S₀) stock.valid sale.2.1 sale.1).integrableC _,
        WilsonMeasuredOwnerIntegrable.original R π Γ Ψ course start live (S₀) R.family.params y (h o p) sale.1 sale.2.1,?_⟩
      intro U
      have e:(W.eval U)⁻¹ • ((h o p).density y (S₀) W U-WilsonMeasuredCoefficientTransport.account (h o p) W U)=
          (h o p).density y (S₀) W U/(W.eval U:ℂ)-(fun _ : Config G (R.family.side t per)=>(0:ℂ)) U-
          WilsonMeasuredCoefficientTransport.account (h o p) W U/(W.eval U:ℂ) := by
        rw [Complex.real_smul,Complex.ofReal_inv];simp only [sub_zero,div_eq_mul_inv];ring
      rw [e]
      exact (fee.2 U).trans (add_le_add (sale.2.2.1.trans (le_abs_self _)) (le_abs_self _))
    · simpa only [d,K,soft,dif_neg p,sub_self,smul_zero,norm_zero] using
        (show Integrable (fun _:Config G (R.family.side t per)=>(0:ℂ)) (prior G _) ∧
          Integrable (fun _:Config G (R.family.side t per)=>(0:ℂ)) (prior G _) ∧
          ∀_:Config G (R.family.side t per),0 ≤ |fees.primary|+|fees.regular| from ⟨by simp,by simp,fun _=>ep⟩)
  rw [D,F]
  refine ⟨?_,?_,?_⟩
  · apply integrable_finsetSum;intro o _;exact (bill o).1.const_mul _
  · apply integrable_finsetSum;intro o _;exact (bill o).2.1.const_mul _
  · intro U
    have same:(W.eval U)⁻¹ • ((∑o,w o*d o U)-∑o,w o*K o U)=∑o,w o*soft o U := by
      simp only [soft,Complex.real_smul]
      rw [mul_sub,Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun o _=>by ring)
    rw [same]
    apply (norm_sum_le _ _).trans
    simp_rw [norm_mul]
    exact WilsonReceivedCompactQUnitLedger.fee test χ measured _ ep (fun o=>soft o U) (fun o=>(bill o).2.2 U)

end YM.Integration.WilsonReceivedQUpperSoft
