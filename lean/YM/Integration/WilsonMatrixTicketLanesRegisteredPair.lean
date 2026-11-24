import YM.Integration.WilsonMatrixTicketLanesRegisteredCovariance
import YM.Integration.WilsonRegisteredRegularQuota

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRegisteredPair
open Function Filter Set MeasureTheory Lattice RG Wilson Source MergeProof Push.Local
open RG12 OPE.Therm Extraction Spec IterationFour PhysicalNext.Repeat.Legato Pert.Asymptotics
open LocalComparison RG3.Script.Picnic Push.SectorMeasure WilsonInheritedRegisteredField
open WilsonMatrixTicketLanesConnectedRegistered WilsonMatrixTicketLanesRegisteredNorm
open WilsonInvariantActionRegisteredReturn WilsonMatrixTicketLanesRegulatorColumn WilsonMatrixTicketLanesRegisteredCovariance
open private measurable from YM.Integration.WilsonMatrixTicketLanesRegisteredLoss
open private product from YM.Integration.WilsonMatrixTicketLanesRegisteredCovariance
open private integral from YM.Integration.WilsonInvariantActionConditionalRegistered
open scoped Topology Classical BigOperators
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
  (F:Spec.Final R.family f S) (L:RG17.Layout F) {k N per:ℕ}

private def normPrice:ℝ:=13+(2:ℝ)^4*stock R 4
private theorem normPrice_pos:0 ≤ normPrice R:=by unfold normPrice stock;positivity

include F L in
private theorem amount (future:k ≤ N) (age:R.family.ref 4 ≤ k) (small:regulatorRun R.family N per k ≤ 1)
    (col:(R.family.path.levels.params k).columns ≤ 4/(regulatorRun R.family N per k)^2)
    (w:R.family.label 4) (x:Site (R.family.side k per)) (e:ℕ) {D:ℝ}
    (input:mass R.family 4 (entry R 4 k N per w) ≤ D/(regulatorRun R.family N per k)^e):
    let g:=regulatorRun R.family N per k
    let A:=(normPrice R*D)/g^(e+4)
    (∀U,‖regular (C:=R.family) R.makes future w x U‖ ≤ A) ∧
    (∀U,‖unmaskedEarlier R k N per future w x U‖ ≤ A):=by
  let g:=regulatorRun R.family N per k
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson future))
  let z:=mass R.family 4 (entry R 4 k N per w)
  have zp:0 ≤ z:=mass_nonneg _ _ _
  have paid:(R.family.S.a k^4)⁻¹*Next.UVStress.quota R.family 4 k N per w=z:=
    (cost R F L 4 k N per age future w).symm
  have up:4/g^2 ≤ 4/g^4:=div_le_div_of_nonneg_left (by norm_num) (pow_pos gp 4)
    (pow_le_pow_of_le_one gp.le small (by decide :2 ≤ 4))
  have hr (U):‖regular (C:=R.family) R.makes future w x U‖ ≤ 12*z/g^4:=by
    have original:=WilsonRegisteredRegularQuota.original (C:=R.family) R.makes future age w x U
    rw [paid] at original
    calc
      _ ≤ _:=original
      _ ≤ 3*(4/g^4)*z:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (col.trans up) (by norm_num)) zp
      _=_:=by ring
  have hmasks (U):‖maskError R future w x U‖ ≤ (1+(2:ℝ)^4*stock R 4)*z/g^4:=
    loss R F L age future small w x U
  have finish:((normPrice R)*z)/g^4 ≤ normPrice R*D/g^(e+4):=by
    calc
      _ ≤ (normPrice R*(D/g^e))/g^4:=div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left input (normPrice_pos R)) (pow_nonneg gp.le _)
      _=_:=by rw [pow_add];ring
  have year:12 ≤ normPrice R:=by
    have extra:0 ≤ (2:ℝ)^4*stock R 4:=by unfold stock;positivity
    unfold normPrice;linarith only [extra]
  constructor
  · intro U;exact (hr U).trans ((div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right year zp) (pow_nonneg gp.le _)).trans finish)
  · intro U
    have diff : unmaskedEarlier R k N per future w x U=regular (C:=R.family) R.makes future w x U-maskError R future w x U:=by
      rw [split R future w x U];ring
    rw [diff]
    exact (norm_sub_le _ _).trans ((add_le_add (hr U) (hmasks U)).trans
      (le_of_eq_of_le (by unfold normPrice;ring) finish))

private theorem add_left {α:Type} [MeasurableSpace α] (μ:Measure α) [IsFiniteMeasure μ]
    (a b h:α→ℂ) (ea:Envelope a) (eb:Envelope b) (eh:Envelope h):
    pair (fun z=>∫U,z U ∂μ) (fun U=>a U+b U) h=
      pair (fun z=>∫U,z U ∂μ) a h+pair (fun z=>∫U,z U ∂μ) b h:=by
  simp only [pair,add_mul]
  rw [integral_add (integral (product ea eh)) (integral (product eb eh)),integral_add (integral ea) (integral eb)]
  ring

private theorem commute {α:Type} (E:(α→ℂ)→ℂ) (u v:α→ℂ):pair E u v=pair E v u:=by
  unfold pair;simp only [mul_comm]

include F L in
/-- The complete earlier physical covariance can use the identical nonlinear fresh
operators plus all earlier signed material. Both measured singleton expectations stay in
the connected subtraction, at arbitrary true placements and future upper cutoff. -/
theorem original (simple:G.Simple) (Y:Poetry R.family.path.levels) (pace:WilsonWindowReportingPace.Slow R.kit)
    (e q:ℕ) {D ε:ℝ} (hD:0 ≤ D) (hε:0<ε):
    ∀ᶠ k:ℕ in atTop,∀ N,(live:k ≤ N)→∀ per,(R.family.ref 4 ≤ k)→∀ (v w:R.family.label 4)
      (x y:Site (R.family.side k per)),
      (mass R.family 4 (entry R 4 k N per v) ≤ D/(regulatorRun R.family N per k)^e)→
      (mass R.family 4 (entry R 4 k N per w) ≤ D/(regulatorRun R.family N per k)^e)→
      let E:=(fun h:Config G (R.family.side k per)→ℂ=>∫U,h U ∂scene R.family.path N per k)
      ‖pair E (regular (C:=R.family) R.makes live v x) (regular (C:=R.family) R.makes live w y)-
        pair E (unmaskedEarlier R k N per live v x) (unmaskedEarlier R k N per live w y)‖ ≤ 
          ε*(regulatorRun R.family N per k)^q:=by
  let C:=normPrice R*D
  have costs:=centered R F L simple Y 4 e (e+4) q hD (C:=C) (mul_nonneg (normPrice_pos R) hD)
    (ε:=ε/2) (half_pos hε)
  filter_upwards [costs,columns R simple pace,WilsonMatrixTicketLanesReportedAccuracy.small R simple 1 zero_lt_one]
    with k sale cols small N live per age v w x y invoice_v invoice_w
  let μ:=scene R.family.path N per k
  letI:IsProbabilityMeasure μ:=probability (p:=per) R.makes.wilson live
  let E:=(fun h:Config G (R.family.side k per)→ℂ=>∫U,h U ∂μ)
  let a:=unmaskedEarlier R k N per live v x
  let b:=unmaskedEarlier R k N per live w y
  let u:=regular (C:=R.family) R.makes live v x
  let h:=regular (C:=R.family) R.makes live w y
  let X:=maskError R live v x
  let Y:=maskError R live w y
  have exd:Envelope u:=regular_envelope (C:=R.family) R.makes live age v x
  have eyd:Envelope h:=regular_envelope (C:=R.family) R.makes live age w y
  have ax:=amount R F L live age (small N per live) (cols N per live) v x e invoice_v
  have by_:=amount R F L live age (small N per live) (cols N per live) w y e invoice_w
  have xenv:Envelope X:=⟨measurable R live v x,_,fun U=>loss R F L age live (small N per live) v x U⟩
  have yenv:Envelope Y:=⟨measurable R live w y,_,fun U=>loss R F L age live (small N per live) w y U⟩
  have am:a=fun U=>u U-X U:=by funext U;dsimp only [a,u,X];rw [split R live v x U];ring
  have bm:b=fun U=>h U-Y U:=by funext U;dsimp only [b,h,Y];rw [split R live w y U];ring
  have aenv:Envelope a:=⟨am ▸ exd.meas.sub xenv.meas,_,ax.2⟩
  have benv:Envelope b:=⟨bm ▸ eyd.meas.sub yenv.meas,_,by_.2⟩
  have am':u=fun U=>a U+X U:=funext (split R live v x)
  have bm':h=fun U=>b U+Y U:=funext (split R live w y)
  have writeA:pair E u h=pair E a h+pair E X h:=by rw [am'];exact add_left μ a X h aenv xenv eyd
  have writeB:pair E a h=pair E a b + pair E Y a:=by
    rw [commute E a h,bm',add_left μ b Y a benv yenv aenv,commute E b a]
  have accounting:pair E u h-pair E a b=pair E X h+pair E Y a:=by rw [writeA,writeB];ring
  dsimp only []
  change ‖pair E u h-pair E a b‖ ≤ _
  rw [accounting]
  exact (norm_add_le _ _).trans ((add_le_add
    (sale N live per age v x invoice_v h eyd.meas by_.1)
    (sale N live per age w y invoice_w a aenv.meas ax.2)).trans_eq (by ring))

end YM.Integration.WilsonMatrixTicketLanesRegisteredPair
