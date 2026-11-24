import YM.Integration.WilsonPositionProgramBlockedTrialNodes
import YM.Integration.WilsonCapturedPrimarySampledPanel
import YM.Integration.WilsonAddressedAlignedPalette
import YM.Next.UV_STRESS.Least
/-! Finite observations of the actual deposited public field. Interpolation uses the
original all-field numerator with its own vacuum. The spatial wrapping error of
its measured axis is kept separately at every positive horizon. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 600000
namespace YM.Integration.WilsonPositionProgramBlockedPublicExperiment
open Function Filter Finset Set Lattice RG Wilson Source Labels Push.Local Extra.Histories
open RG05Readout.Records
open Next.Foundations ProjectorNext.Equivariance Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Pert.Asymptotics Stationary Comparison.RG02 RG16 RG16.Literal
open WilsonCapturedPrimaryAperture WilsonCapturedPrimaryPotential WilsonCapturedPrimaryPaid
open WilsonCapturedPrimaryReading WilsonCapturedPrimaryCollar WilsonFirstReceivedRadialStencil Next.Rank
open WilsonCapturedPrimaryCoreBill (wrapFee)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G)(d:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "B₀" => (C₀).localSection d
local notation "H₀" => (C₀).path
local notation "P₀" => (C₀).params
def deposited (N p j:ℕ)(x:(C₀).label d):Coefficient F₀ ((C₀).side j p):=
  let T:=(C₀).factory d N p
  T.entries j (T.terminal.symm x)
def ray (N p j target:ℕ)(a:Probe G d)(z:ℝ):Config G ((C₀).side j p):=
  let b:=(H₀).levels.budget j
  let g:=regulatorRun C₀ N p (j+1)
  let r:=radius b (cutoff b g (grade target d 1))
  Integral.sample g (Stationary.arm G ((C₀).side j p) 1 (lifted P₀ b 0 r a g z))
def observed {N p j:ℕ}(live:j≤N)(x:(C₀).label d)(U:Config G ((C₀).side j p)):ℂ:=
  dyes C₀ j N p live (((C₀).S.a j:ℂ)^d • (C₀).O N p x 0) U/(((H₀).rep N p j).eval U:ℂ)
def polynomial {N p j:ℕ}(live:j≤N)(target:ℕ)(x:(C₀).label d)(a:Probe G d):Polynomial ℂ:=
  let g:=regulatorRun C₀ N p (j+1)
  let t:=g^gap target 1
  WilsonCapturedPrimarySampledPanel.sample d t (fun i=>observed R d (p:=p) live x (ray R d N p j target a (t*node d i)))
def recovery {N p j:ℕ}(live:j≤N)(target:ℕ)(x:(C₀).label d): (C₀).label d:=
  WilsonCapturedPrimaryDecoder.forecast F₀ (polynomial R d (p:=p) live target x)

theorem actual {N p j:ℕ}(live:j≤N)(ready:(C₀).ref d≤j)(x:(C₀).label d)(U:Config G ((C₀).side j p)):
    observed R d (p:=p) live x U=reading B₀ ((H₀).rep N p j) 0 (deposited R d N p j x) U:=by
  have eq:=WilsonAddressedAlignedPalette.density R (p:=p) live ready (((C₀).factory d N p).terminal.symm x)
  rw [LinearEquiv.apply_symm_apply] at eq
  unfold observed reading
  exact congrArg (fun a:ℂ=>a/(((H₀).rep N p j).eval U:ℂ)) (congrFun eq U).symm

theorem original (simple:G.Simple) (wide:∀ j,1≤((H₀).levels.budget j).supportExponent) (target:ℕ):
    ∀ᶠ j:ℕ in atTop,∀ N p,∀ later:j+1≤N,∀ x:(C₀).label d,
      let live:=Nat.le_trans (Nat.le_succ j) later
      let e:=(deposited R d N p j x).x
      let W:=(H₀).rep N p j
      let g:=regulatorRun C₀ N p (j+1)
      let c:=((H₀).levels.params j).columns
      let h:=Next.UVStress.quota (C₀) d j N p x
      (F₀).coeffSize (e-recovery R d (p:=p) live target x)≤
        wrapFee F₀ P₀*wraps W.p ((C₀).side j p)*(c*h)+
        WilsonCapturedPrimaryDecoder.invoice F₀ P₀ d*(2*c*h)*g^target:=by
  filter_upwards [WilsonCapturedPrimaryOnRun.readouts R simple F₀ P₀ B₀ target 0 1 le_rfl,
    eventually_ge_atTop (R.t d),eventually_ge_atTop ((C₀).ref d)] with j test ready ref
  intro N p later x live e W g c h
  let q:=deposited R d N p j x
  have level:W.p=(H₀).levels.budget j:=(R.makes.wilson.represents N p j live).vac
  obtain ⟨read,ranks⟩:=WilsonCapturedPrimarySection.original R ready W level
  have cal:=R.makes.calibrated d N p (ref.trans live)
  have form:=cal.format j ref live (((C₀).factory d N p).terminal.symm x)
  have rough:=cal.cap j ref live (((C₀).factory d N p).terminal.symm x)
  let s:=c*(F₀).coeffSize ((F₀).core q.x)
  let projected:=projection F₀ P₀ W.p.threshold 0 q
  have pos:0≤c:=zero_le_one.trans ((H₀).levels.params j).columns_ge
  have sh:s≤c*h:=mul_le_mul_of_nonneg_left (Work.G08.size_core F₀ q.x) pos
  have hp:0≤h:=Work.G08.size_nonneg F₀ q.x
  have gw:0<g:=ActualRunKernelPackets.regulator_pos R N p (j+1) later
  let I:=WilsonCapturedPrimaryDecoder.invoice F₀ P₀ d
  let y:=polynomial R d (p:=p) live target x
  have deg (a): (y a).natDegree≤d:=WilsonCapturedPrimarySampledPanel.degree d (pow_ne_zero _ gw.ne') _
  have readings:=test N p later (wide j) (level ▸ ranks) W level 0 q _ _ _ (2*c*h) read form rough
    (by positivity) (by simp only [pow_zero,div_one];change s+s≤2*c*h;linarith) d le_rfl y (fun a _=>deg a)
  have nodes:=readings (by
    intro a ha i hi z X angle hb hi' zero
    have eq:=WilsonCapturedPrimarySampledPanel.at_node d (pow_ne_zero (gap target 1) gw.ne')
       (fun k=>observed R d (p:=p) live x (ray R d N p j target a (g^gap target 1*node d k))) hi
    change ‖reading B₀ W 0 q _-(y a).eval _‖≤_
    rw [show (y a).eval (z:ℂ)=observed R d (p:=p) live x (Integral.sample g angle) from eq,
      actual R d (p:=p) live ref x]
    change ‖reading B₀ W 0 q _-reading B₀ W 0 q _‖≤_
    rw [sub_self,norm_zero];positivity)
  have cash:0≤(2*c*h)*g^target:=by positivity
  have decoded:=WilsonCapturedPrimaryDecoder.returned F₀ P₀ d projected y cash
    (fun a ha=>by simpa only [mul_assoc] using nodes a ha)
  have seam:= (germ_close F₀ P₀).choose_spec.2 W q form rough read.order read.power
  have field:(F₀).coeffSize (e-projected)≤wrapFee F₀ P₀*wraps W.p ((C₀).side j p)*(c*h):=calc
    _ ≤ ((F₀).extra+1:ℕ)*‖e-projected‖:=size_le_norm F₀ _
    _ = ((F₀).extra+1:ℕ)*‖projected-e‖:=by rw [norm_sub_rev]
    _ ≤ ((F₀).extra+1:ℕ)*((germ_close F₀ P₀).choose*wraps W.p ((C₀).side j p)*s):=
      mul_le_mul_of_nonneg_left seam (Nat.cast_nonneg _)
    _ = wrapFee F₀ P₀*wraps W.p ((C₀).side j p)*s:=by unfold wrapFee;ring
    _ ≤ _:=mul_le_mul_of_nonneg_left sh (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (germ_close F₀ P₀).choose_spec.1.le) (Real.exp_pos _).le)
  calc
    _ ≤ (F₀).coeffSize (e-projected)+(F₀).coeffSize (projected-recovery R d (p:=p) live target x):=by
      unfold Frame.coeffSize
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_le_sum;intro i hi
      change ‖e i-_‖≤‖e i-projected i‖+‖projected i-_‖
      simpa only [dist_eq_norm] using dist_triangle (e i) (projected i) (recovery R d (p:=p) live target x i)
    _ ≤ _:=add_le_add field (by simpa only [recovery,I,y,mul_assoc] using decoded)
end YM.Integration.WilsonPositionProgramBlockedPublicExperiment
end
