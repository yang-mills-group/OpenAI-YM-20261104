import YM.Integration.WilsonPositionProgramBlockedTrialAddBack
import YM.Integration.WilsonCapturedPrimaryOnRun
import YM.Integration.WilsonCapturedPrimarySection
import YM.Integration.WilsonCapturedPrimaryDecoder
/-! Finite real probes for the solved Wilson trial. The original received
primary and remainder supply their own invoice. Only the signed node return
of the independently filed material is tested, before either regulator. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonPositionProgramBlockedTrialNodes
open Function Filter Finset Set Lattice RG Wilson Source Labels Push.Local Extra.Histories
open Next.Foundations ProjectorNext.Equivariance Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Pert.Asymptotics Stationary Comparison.RG02 RG16 RG16.Literal
open WilsonCapturedPrimaryAperture WilsonCapturedPrimaryPotential WilsonCapturedPrimaryPaid
open WilsonCapturedPrimaryReading WilsonCapturedPrimaryCollar WilsonFirstReceivedRadialStencil
open scoped Classical Topology BigOperators

variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "B₀" => (C₀).localSection d
local notation "H₀" => (C₀).path
local notation "P₀" => (C₀).params

def originalRent (b:ℕ) (e:(C₀).label d):ℝ:=
  2*(((H₀).levels.params b).columns+stock C₀ b)*(F₀).coeffSize e

def Samples (N p b target D:ℕ)(e:(C₀).label d)(q:Coefficient F₀ ((C₀).side b p))
    (y:Probe G d→Polynomial ℂ)(extra:ℝ):Prop:=
  let W:=(H₀).rep N p b
  let g:=regulatorRun C₀ N p (b+1)
  let Q:=grade target d 1
  let budget:=(H₀).levels.budget b
  let r:=radius budget (cutoff budget g Q)
  ∀ a∈tests F₀,∀ j≤D,
    let z:=g^gap target 1*node D j
    let X:=lifted P₀ budget (0:Site ((C₀).side b p)) r a g z
    let angle:=Stationary.arm G ((C₀).side b p) 1 X
    |bound G budget g 1|≤(budget.B:ℝ)^2*budget.threshold/g →
    (∀ l,‖Exterior.collect G angle l‖≤1*|bound G budget g 1|) →
    flags W.p.threshold (Integral.sample g angle)=∅ →
    ‖reading B₀ W 0 q (Integral.sample g angle)-(y a).eval (z:ℂ)‖ ≤ (originalRent R d b e+extra)*g^Q

def Invoice (N p b target:ℕ)(e:(C₀).label d)(q:Coefficient F₀ ((C₀).side b p)):Prop:=
  ∀ (extra:ℝ),0≤extra → ∀ D,d≤D → ∀ y:Probe G d→Polynomial ℂ,(∀ a∈tests F₀,(y a).natDegree≤D) →
  Samples R d N p b target D e q y extra →
  (F₀).coeffSize (gMap C₀ N p d b (e-WilsonCapturedPrimaryDecoder.forecast F₀ y)) ≤
    2^(degree F₀)*WilsonCapturedPrimaryDecoder.invoice F₀ P₀ D*(originalRent R d b e+extra)*(regulatorRun C₀ N p (b+1))^target

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀ j,1≤((H₀).levels.budget j).supportExponent) (target:ℕ){η:ℝ} (ep:0<η):
    ∀ᶠ b:ℕ in atTop,∀ N p n,∀ live:b+n≤N,b+1≤N→let W:=(H₀).rep N p b
      let out:=WilsonPositionProgramOriginalBlockedTrial.carried R d (p:=p) live 0
      ∃ A:(C₀).label d ≃ₗ[ℂ] (C₀).label d,∀ e:(C₀).label d,let w:=A.symm e
        (F₀).coeffSize w ≤ 2*Real.exp (η*((C₀).S.scale (b+n)-(C₀).S.scale b))*(F₀).coeffSize e ∧
        ∃ q:Coefficient F₀ ((C₀).side b p),q.Format 0 P₀ W ∧
          q.remBound 0 W (safety C₀ b) (2*stock C₀ b*(F₀).coeffSize e) ∧ q.density 0 B₀ W=out w ∧
          projection F₀ P₀ W.p.threshold 0 q=e ∧ Invoice R d N p b target e q:=by
  filter_upwards [WilsonPositionProgramBlockedTrialSalary.original R shop d simple ep,
    WilsonCapturedPrimaryOnRun.readouts R simple F₀ P₀ B₀ target 0 1 le_rfl,eventually_ge_atTop (R.t d)] with b salary test ready
  intro N p n live hi W out
  have now:b≤N:=by omega
  have date:W.p=(H₀).levels.budget b:=(R.makes.wilson.represents N p b now).vac
  obtain ⟨read,level⟩:=WilsonCapturedPrimarySection.original R ready W date
  obtain ⟨A,issued⟩:=salary N p n live
  refine ⟨A,?_⟩;intro e w
  obtain ⟨fare,q,form,rough,peak,held,proj⟩:=issued e
  refine ⟨fare,q,form,rough,held,proj,?_⟩
  intro extra nn D rk y degree sampled
  let g:=regulatorRun C₀ N p (b+1)
  let cap:=originalRent R d b e+extra
  have col:0≤((H₀).levels.params b).columns:=zero_le_one.trans ((H₀).levels.params b).columns_ge
  have sr:0≤2*stock C₀ b*(F₀).coeffSize e:=by obtain ⟨x,y,hx,hy,he,_⟩:=rough;linarith
  have pc:((H₀).levels.params b).columns*(F₀).coeffSize ((F₀).core q.x) ≤
      ((H₀).levels.params b).columns*(2*(F₀).coeffSize e):=
    mul_le_mul_of_nonneg_left ((Work.G08.size_core _ _).trans peak) col
  have price:((H₀).levels.params b).columns*(F₀).coeffSize ((F₀).core q.x)+2*stock C₀ b*(F₀).coeffSize e≤cap:=by
    dsimp only [cap,originalRent];nlinarith only [pc,nn]
  have pos:0≤cap:=le_trans (add_nonneg (mul_nonneg col (Work.G08.size_nonneg ..)) sr) price
  have readings:=test N p hi (wide b) (date ▸ level) W date 0 q _ _ _ cap read form rough pos
    (by simpa using price) D rk y degree sampled
  have hu:0≤g:=by change 0≤(Real.sqrt _)⁻¹; positivity
  have dec:=WilsonCapturedPrimaryDecoder.returned F₀ P₀ D (projection F₀ P₀ W.p.threshold 0 q) y
    (L:=cap*g^target) (mul_nonneg pos (pow_nonneg hu _)) (fun a ha=>by simpa only [mul_assoc] using readings a ha)
  rw [proj] at dec
  exact (WilsonMasterCoordinatePrice.positive_grade R.makes N p d b now _).trans
    ((mul_le_mul_of_nonneg_left dec (by positivity)).trans_eq (by simp only [cap,g,mul_assoc];rfl))

end YM.Integration.WilsonPositionProgramBlockedTrialNodes
end
