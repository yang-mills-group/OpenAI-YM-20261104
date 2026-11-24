import YM.Integration.WilsonOriginalAlternativeTrialRegistered
import YM.Integration.WilsonOriginalAlternativeTrialAnyFiled

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialAnyIncome
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory Source Labels
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato PhysicalNext.Repeat.Boulevard
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonThermometerSolitaryRegularHead WilsonThermometerSolitaryFiledExchange WilsonThermometerSolitaryExchange
open Comparison.RG02.Cumulants WilsonOriginalOccupiedTap
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N per m k t u:ℕ}
    (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
local notation "F" i:max => Config G (R.family.side i per)
variable {V:Type}[DecidableEq V][Fintype V]{J:Census V}
local notation "P" => Ψ t
variable {X I:Type}[Countable I]

include course in
theorem original (mt:m ≤ t)(tn:t ≤ N)(o:V → Site (R.family.side t per))
    (A:Gallery X I o P (J))(w:V→ℝ)(wp:∀v,0<w v)
    (base:A.E.Paid w (P).p.B (P).p.supportExponent 1){K:ℝ}
    (hard:A.K.Paid w (P).p.B (P).p.supportExponent K)(x:X)(s:(J).Mode):
    let full:=fun U:F t=>(A.density x U).part s/((P).eval U:ℂ)
    let model:=fun U:F t=>∏j∈s.val,(A.E.log x U).part (J.fire j)
    Integrable (fun U=>(R.family.path.rep N per t).eval U • full U) (prior G _) ∧
      Integrable (fun U=>(R.family.path.rep N per t).eval U • model U) (prior G _):=by
  intro full model
  let vacuum:=fun U:F t=>((P).eval U:ℂ)
  have quiet:(P).eval=(R.family.path.rep N per t).eval:=(later R π Γ Ψ course mt tn).view
  have nz (U:F t):vacuum U≠0:=by
    unfold vacuum;rw [quiet];exact Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive R.makes.wilson tn U).ne'
  have law:=(course.1.walk t mt tn).truep.valid
  let O:=WilsonPrecontactSeparatedLamps.portion A.E (WilsonPrecontactSeparatedLamps.mixed A.E)ᶜ
  have cut:=WilsonPrecontactSeparatedLamps.charged A.E (WilsonPrecontactSeparatedLamps.mixed A.E)ᶜ base
  let due:=(fun B:F t→ℂ=>Integrable (fun U=>(R.family.path.rep N per t).eval U • B U) (prior G _))
  have regular {D:Type}[Countable D](L:Lamps X D G (P).p o (J)) (paid:L.Paid w (P).p.B (P).p.supportExponent 1):
      due (fun U=>(Poly.pass (L.log x U)).part s):=by
    let B:Gallery X D o P (J):=⟨L,A.K⟩
    have rent:(gallery 0 B).K.Paid w (P).p.B (P).p.supportExponent K:=by
      simpa only [gallery,one_mul] using WilsonOriginalOccupiedTap.paid B.K 0 (le_refl (1:ℝ)) (by simp) wp hard
    have income:=QuadraticLocal.Tariff.integrable (J) o w wp (gallery 0 B) x ⟨paid,rent⟩ (P).p.exponent_pos.le law
    have field (U:F t):((gallery 0 B).density x U).part s=(R.family.path.rep N per t).eval U • (Poly.pass (L.log x U)).part s:=by
      rw [WilsonOriginalOccupiedWallet.origin B x U w wp rent,Poly.part_smul,quiet,Complex.real_smul]
    dsimp only [due]
    rw [show (fun U=>(R.family.path.rep N per t).eval U • (Poly.pass (L.log x U)).part s)=_ from funext (fun U=>(field U).symm)]
    exact (Poly.get s).integrable_comp income
  have posted (U:F t):(Poly.pass (O.log x U)).part s=model U:=
    WilsonOriginalAlternativeTrialAnyFiled.original A.E wp base x U s
  have ordinary:due model:=by
    rw [←show (fun U=>(Poly.pass (O.log x U)).part s)=model from funext posted]
    exact regular O cut
  have whole:due full:=by
    have paid:=QuadraticLocal.Tariff.integrable (J) o w wp A x ⟨base,hard⟩ (P).p.exponent_pos.le law
    have same (U:F t):(R.family.path.rep N per t).eval U • full U=(A.density x U).part s:=by
      rw [←quiet,Complex.real_smul]
      change vacuum U*((A.density x U).part s/vacuum U)=_
      field_simp [nz U]
    change Integrable _ _
    rw [show (fun U=>(R.family.path.rep N per t).eval U • full U)=_ from funext same]
    exact (Poly.get s).integrable_comp paid
  exact ⟨whole,ordinary⟩

end YM.Integration.WilsonOriginalAlternativeTrialAnyIncome
end
