import YM.Integration.WilsonPositionProgramBlockedPublicExperiment
import YM.Integration.WilsonPositionProgramBlockedTrialInverse

/-! Use the full germ projection of the measured physical coefficient as the
target. Its difference from the bare coordinate has its original period wrap.
The unaltered weak-field sampler hears this target directly. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicGuardedPage
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

open WilsonPositionProgramBlockedPublicExperiment RG05Readout RG05Readout.Address

def full (N p j:ℕ)(x:(C₀).label d):(C₀).label d:=
  projection F₀ P₀ ((H₀).rep N p j).p.threshold 0 (deposited R d N p j x)

theorem page_at {N p j:ℕ}(live:j ≤ N)(x:(C₀).label d):
    full R d N p j x = page (C:=C₀) d p j (deposited R d N p j x):=by
  unfold full
  have level:((H₀).rep N p j).p=plank C₀ j:=(R.makes.wilson.represents N p j live).vac
  rw [level]

def wrapCost (j:ℕ):ℝ:=
  wrapFee F₀ P₀*Real.exp (2*((H₀).levels.budget j).supportExponent)*((H₀).levels.params j).columns

theorem wage {N p j:ℕ}(ready:R.t d ≤ j)(ref:(C₀).ref d ≤ j)(live:j ≤ N)
    (wide:1 ≤ ((H₀).levels.budget j).supportExponent)(x:(C₀).label d):
    let q:=deposited R d N p j x
    let e:=full R d N p j x
    let c:=((H₀).levels.params j).columns
    (F₀).coeffSize (e-q.x) ≤ wrapFee F₀ P₀*wraps ((H₀).rep N p j).p ((C₀).side j p)*(c*(F₀).coeffSize q.x) ∧
    (F₀).coeffSize e ≤ (1+wrapCost R d j)*(F₀).coeffSize q.x:=by
  intro q e c
  let W:=(H₀).rep N p j
  have level:W.p=(H₀).levels.budget j:=(R.makes.wilson.represents N p j live).vac
  obtain ⟨read,_⟩:=WilsonCapturedPrimarySection.original R ready W level
  have cal:=R.makes.calibrated d N p (ref.trans live)
  have form:=cal.format j ref live (((C₀).factory d N p).terminal.symm x)
  have rough:=cal.cap j ref live (((C₀).factory d N p).terminal.symm x)
  let D:=(germ_close F₀ P₀).choose
  let h:=(F₀).coeffSize q.x
  have written:= (germ_close F₀ P₀).choose_spec.2 W q form rough read.order read.power
  have hp:0 ≤ c:=zero_le_one.trans ((H₀).levels.params j).columns_ge
  have hpos:0 ≤ h:=Work.G08.size_nonneg F₀ q.x
  have price:0 ≤ wrapFee F₀ P₀:=mul_nonneg (Nat.cast_nonneg _) (germ_close F₀ P₀).choose_spec.1.le
  have f:(F₀).coeffSize (e-q.x) ≤ wrapFee F₀ P₀*wraps W.p ((C₀).side j p)*(c*h):=calc
    _ ≤ ((F₀).extra+1:ℕ)*‖e-q.x‖:=size_le_norm F₀ _
    _ ≤ ((F₀).extra+1:ℕ)*(D*wraps W.p ((C₀).side j p)*(c*(F₀).coeffSize ((F₀).core q.x))):=
      mul_le_mul_of_nonneg_left written (Nat.cast_nonneg _)
    _ = wrapFee F₀ P₀*wraps W.p ((C₀).side j p)*(c*(F₀).coeffSize ((F₀).core q.x)):=by unfold wrapFee D;ring
    _ ≤ _:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Work.G08.size_core F₀ q.x) hp)
      (mul_nonneg price (Real.exp_nonneg _))
  have wrap:wraps W.p ((C₀).side j p) ≤ Real.exp (2*((H₀).levels.budget j).supportExponent):=by
    unfold Germ.wraps
    rw [level]
    apply Real.exp_le_exp.mpr
    apply sub_le_self
    have ha:0 ≤ ((H₀).levels.budget j).supportExponent:=zero_le_one.trans wide
    positivity
  refine ⟨f,?_⟩
  have total:=Size.add F₀ (e-q.x) q.x
  rw [sub_add_cancel] at total
  have cost:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left wrap price) (mul_nonneg hp hpos)
  change (F₀).coeffSize e ≤ (1+_)*h
  have sum:=add_le_add (f.trans cost) (le_refl h)
  exact (total.trans sum).trans_eq (by unfold wrapCost;ring)

theorem sampled (simple:G.Simple)(wide:∀j,1 ≤ ((H₀).levels.budget j).supportExponent)(target:ℕ):
    ∀ᶠ j:ℕ in atTop,∀N p,∀later:j+1 ≤ N,∀ x:(C₀).label d,
      let live:=Nat.le_trans (Nat.le_succ j) later
      let q:=deposited R d N p j x
      let read:=full R d N p j x
      let g:=regulatorRun C₀ N p (j+1)
      let c:=((H₀).levels.params j).columns
      let h:=(F₀).coeffSize q.x
      (F₀).coeffSize (read-recovery R d (p:=p) live target x) ≤
        WilsonCapturedPrimaryDecoder.invoice F₀ P₀ d*(2*c*h)*g^target:=by
  filter_upwards [WilsonCapturedPrimaryOnRun.readouts R simple F₀ P₀ B₀ target 0 1 le_rfl,
    eventually_ge_atTop (R.t d),eventually_ge_atTop ((C₀).ref d)] with j test ready ref
  intro N p later x live q seenP g c h
  let W:=(H₀).rep N p j
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
  change (F₀).coeffSize (projected-recovery R d (p:=p) live target x) ≤ _
  exact decoded.trans_eq (by ring)

end YM.Integration.WilsonOriginalMicroscopicGuardedPage
end
