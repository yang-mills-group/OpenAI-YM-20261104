import YM.Integration.WilsonOriginalAlternativeTrialRegistered
import YM.Integration.WilsonOriginalAlternativeTrialAnyFiled

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialAnyCharge
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
theorem original (mu:m ≤ u)(ut:u ≤ t)(tn:t ≤ N)(o:V → Site (R.family.side t per))
    (A:Gallery X I o P (J))(w:V→ℝ)(wp:∀v,0<w v)
    (wide:5 ≤ (P).p.B)(apart:∀v k:V,v≠k→(P).p.B^2+1 ≤ separation (o v) (o k))
    (reg:A.E.Paid w (P).p.B ((P).p.supportExponent+2) 1){K:ℝ}
    (hard:A.K.Paid w (P).p.B (P).p.supportExponent K)(x:X)(s:(J).Mode)(W:F u):
    let full:=fun U:F t=>(A.density x U).part s/((P).eval U:ℂ)
    let model:=fun U:F t=>∏j∈s.val,(A.E.log x U).part (J.fire j)
    let spent:=fun U:F t=>((A.density x U).part s-((P).eval U:ℂ)*(Poly.pass (A.E.log x U)).part s)/((P).eval U:ℂ)
    ‖actualTransport R.family (N:=N) (fun U=>full U-model U) ut W‖ ≤
      ‖actualTransport R.family (N:=N) spent ut W‖+
        ((shards J s).card:ℝ)*Real.exp (-(2:ℝ)*(((P).p.B/8:ℕ):ℝ))/Poly.toll w s:=by
  intro full model spent
  let vacuum:=fun U:F t=>((P).eval U:ℂ)
  let clean:=fun U:F t=>(Poly.pass (A.E.log x U)).part s
  have quiet:(P).eval=(R.family.path.rep N per t).eval:=(later R π Γ Ψ course (mu.trans ut) tn).view
  have nz (U:F t):vacuum U≠0:=by
    unfold vacuum;rw [quiet];exact Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive R.makes.wilson tn U).ne'
  have law:=(course.1.walk t (mu.trans ut) tn).truep.valid
  have base:=WilsonPrecontactSeparatedLamps.lower A.E (show (P).p.supportExponent≤(P).p.supportExponent+2 by linarith) wp reg
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
  have soft:due clean:=regular A.E base
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
  have removable:spent=fun U=>full U-clean U:=by
    funext U
    change ((A.density x U).part s-vacuum U*clean U)/vacuum U=(A.density x U).part s/vacuum U-clean U
    field_simp [nz U]
  let flow:=(fun B:F t→ℂ=>actualTransport R.family (N:=N) B ut W)
  have split (a b:F t→ℂ)(pa:due a)(pb:due b):flow (fun U=>a U-b U)=flow a-flow b:=
    congrFun (ActualWilsonAbsoluteTransport.sub R.family R.makes tn pa pb ut) W
  have gap:‖flow (fun U=>clean U-model U)‖≤
      ((shards J s).card:ℝ)*Real.exp (-(2:ℝ)*(((P).p.B/8:ℕ):ℝ))/Poly.toll w s:=by
    apply actualTransport_norm_le R.family R.makes tn _ ut
    intro U
    apply (le_div_iff₀ (Poly.worth wp s)).2
    simpa only [clean,model,mul_comm (Poly.toll w s)] using
      WilsonOriginalAlternativeTrialAnyFiled.rated A.E wp wide apart reg x U s
  change ‖flow (fun U=>full U-model U)‖≤‖flow spent‖+_
  rw [split full model whole ordinary,removable,split full clean whole soft]
  rw [split clean model soft ordinary] at gap
  calc ‖flow full-flow model‖ = ‖(flow full-flow clean)+(flow clean-flow model)‖:=by rw [sub_add_sub_cancel]
       _ ≤ _ := (norm_add_le ..).trans (add_le_add le_rfl gap)

end YM.Integration.WilsonOriginalAlternativeTrialAnyCharge
end
