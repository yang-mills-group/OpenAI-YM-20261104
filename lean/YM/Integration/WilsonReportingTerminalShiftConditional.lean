import YM.Integration.WilsonReportingTerminalShiftPrice
import YM.Integration.WilsonLocalReportingL1

/-! Pay the absolute first moment of the complete translated profile remainder
on the original single-step conditional, including an arbitrary retained event. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportingTerminalShiftConditional
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Extraction Spec RG12 RG17
open RG05Readout Address Native Pulse WilsonReportingTerminalShiftPrice
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {T:YM.Table C.book} {F:Final C f T}
  (L:Layout F) {I:Type} [Fintype I] (d:I→ℕ) (w:(i:I)→C.label (d i))

def component (imag:Bool) (z:ℂ):ℝ:=if imag then z.im else z.re

private theorem part_bound (imag:Bool) (z:ℂ):‖component imag z‖≤‖z‖:=by
  cases imag with
  | false => exact Complex.abs_re_le_norm z
  | true => exact Complex.abs_im_le_norm z

def signed (φ:Wave I) (r:ℝ) (m per k:ℕ) (y:Cloud I) (child:I→Bud C per m)
    (o:I→Site (C.side (m+1) per)) (imag:Bool) (U:Config G (C.side (m+1) per)) : ℝ:=
  component imag (error L d w φ r m per k y child o U)

theorem reading (φ:Wave I) (r A:ℝ) (t per k:ℕ) (y:Cloud I) (child:I→Bud C per t)
    (o:I→Site (C.side (t+1) per)) (paid : ∀U,‖error L d w φ r t per k y child o U‖≤fare L d w r A t k)
    (imag:Bool) :
    let H:=signed L d w φ r t per k y child o imag
    Envelope H ∧ GaugeInvariant H ∧ ∀E:Set (Config G (C.side (t+1) per)),∀V:Config G (C.side t per),
      actualAverage C (N:=t+1) (E.indicator (fun U=>‖H U‖)) V≤fare L d w r A t k := by
  let v:Cloud I:=fun i=>displacement C per t (child i)
  let z:ℂ := φ.val (y+(C.S.a t/r) • v)-WilsonReportingCellTaylorRemainder.jet φ k y v (C.S.a t/r)
  let H:=signed L d w φ r t per k y child o imag
  have observed (U):‖H U‖≤fare L d w r A t k:=(part_bound imag _).trans (paid U)
  have whole:Continuous (error L d w φ r t per k y child o):=by
    change Continuous (fun U=>z*∏i,C.O (t+1) per (atRef L (d i) r (t+1,per) (w i)) (o i) U)
    exact continuous_const.mul (continuous_finsetProd _ fun i _=>C.continuousO ..)
  have continuousH:Continuous H:=by
    cases imag with
    | false => exact Complex.continuous_re.comp whole
    | true => exact Complex.continuous_im.comp whole
  refine ⟨⟨continuousH.measurable,_,observed⟩,?_,?_⟩
  · intro a U
    change component imag (z*_) = component imag (z*_)
    apply congrArg (fun x:ℂ=>component imag (z*x))
    exact Finset.prod_congr rfl (fun i _=>C.invariant F.room.cutoff _ _ _ _ _ a U)
  · intro E V
    apply (le_abs_self _).trans (actualAverage_norm_le C F.room.cutoff t.lt_succ_self
      (F:=E.indicator (fun U=>‖H U‖)) (B:=fare L d w r A t k) _ V)
    intro U
    by_cases h:U∈E
    · simpa only [indicator_of_mem h,norm_norm] using observed U
    · simpa only [indicator_of_notMem h,norm_zero] using (norm_nonneg (H U)).trans (observed U)

variable (R:Run G) {M:YM.Table R.family.book} {F':Final R.family f M} (layout:Layout F')
  (labels:(i:I)→R.family.label (d i))

def income (r A:ℝ) (k:ℕ):ℝ:=
  A*(4*R.family.S.a (layout.level r)/r)^(k+1)*2^(ranks R.family d)*budget layout d labels r

theorem account (simple:G.Simple)
    (slow:∀j,((R.family.S.block j).val:ℝ)≤Real.log (RG05Readout.Lambda R.family.path.levels j))
    (r A:ℝ) (rp:0<r) (ap:0≤A) (t per k:ℕ) :
    (regulatorRun R.family (t+1) per (t+1))^(2*((k+1)+ranks R.family d))*fare layout d labels r A t k≤
      income (R:=R) (d:=d) (layout:=layout) (labels:=labels) r A k := by
  let levels:=R.family.path.levels
  let β:=levels.clock.hatBeta (t+1)
  let h:=levels.clock.hatBeta t
  let b:=R.family.path.β (t+1) per (t+1)
  let g:=regulatorRun R.family (t+1) per (t+1)
  let a:=R.family.S.a (layout.level r)
  let ℓ:ℝ:=(R.family.S.block t).val
  have hp:1≤h:=(levels.fits.delayed t).le
  have hp':0<h:=zero_lt_one.trans_le hp
  have mono:=WilsonStartup.Timing.hat_mono levels (Gauge.slopeConstant_pos simple).le
  have current:h≤β:=mono t.le_succ
  have β0:0≤β:=hp'.le.trans current
  have gb:0≤g^2*β:=mul_nonneg (sq_nonneg _) β0
  have hot:β/2≤b:=(R.makes.wilson.represents (t+1) per (t+1) le_rfl).band.1
  have bp:0<b:=by linarith
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr bp)
  have ratio:ℓ≤2*β:=by
    have hh:0≤Real.log h:=Real.log_nonneg hp
    have hh':Real.log h≤h-1:=Real.log_le_sub_one_of_pos hp'
    have he:Real.log (2+Real.log h)≤2+Real.log h-1:=Real.log_le_sub_one_of_pos (by linarith)
    have step:ℓ≤Real.log (2+Real.log h):=slow t
    linarith only [hp,current,step,he,hh']
  have g2:g^2=1/b:=by
    change (Real.sqrt b)⁻¹^2=1/b
    rw [inv_pow,Real.sq_sqrt bp.le,one_div]
  have temp:g^2*β≤2:=by rw [g2,one_div,inv_mul_eq_div];exact (div_le_iff₀ bp).2 (by linarith only [hot])
  have block:g^2*ℓ≤4:=(mul_le_mul_of_nonneg_left ratio (sq_nonneg _)).trans (by linarith only [temp])
  have gA:0<a:=R.family.S.a_pos _
  have preserve:g^2*(a*ℓ/r)≤4*a/r:=by
    calc g^2*(a*ℓ/r)=(g^2*ℓ)*(a/r):=by ring
         _≤4*(a/r):=mul_le_mul_of_nonneg_right block (div_pos gA rp).le
         _=4*a/r:=by ring
  have hm:0≤budget layout d labels r:=Finset.prod_nonneg fun i _=>
    mul_nonneg (zero_le_one.trans (Extra.Multi.BasisCost.price_pos _)) (mass_nonneg ..)
  change g^(2*((k+1)+ranks R.family d))*(A*(a*ℓ/r)^(k+1)*β^ranks R.family d*budget layout d labels r)≤_
  calc _=A*(g^2*(a*ℓ/r))^(k+1)*(g^2*β)^(ranks R.family d)*budget layout d labels r:=by
           rw [pow_mul,pow_add,mul_pow,mul_pow];ring
       _≤A*(4*a/r)^(k+1)*2^(ranks R.family d)*budget layout d labels r:=by
           gcongr
       _=income (R:=R) (d:=d) (layout:=layout) (labels:=labels) r A k:=rfl
end YM.Integration.WilsonReportingTerminalShiftConditional
