import YM.Integration.WilsonReflectedPublicSignedCoefficient
/-! Both signed replacements at a fixed physical cutoff have the requested
reported order after paying the true angle, the physical engineering and the original forcing. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicSignedFare
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Trace.Physical Trace.Physical.GermGraph Push Push.Local Marker Motion PhysicalNext PhysicalNext.Repeat.Legato
open Trace.Physical.Germ
open Planned.GuardedAtom MergeProof MergeProof.Accent Extra.Multi RG05Readout RG05Readout.Address
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonThermometerReflectedTrajectory
open scoped Topology BigOperators Classical
open WilsonReflectedFundedHearing WilsonReflectedOpticalArm
variable {G:Gauge}(R:Run G){N p f K d:ℕ}
local notation "C₀" => R.family
local notation "F" => R.family.labels.level d
local notation "P₁" => R.family.path.rep N p f

local notation "β" => R.alloy.B.a.clock.hatBeta
structure Restored (A:Arm R d N p f K) (begin:f≤K)(live:K≤N)(c:ℂ)(cash:ℝ)
    (q:Coefficient (F) ((C₀).side f p)) : Prop where
  form:q.Format A.o (C₀).params (P₁)
  paid:q.remBound A.o (P₁) (safety (C₀) f) cash
  primary:(F).coeffSize q.x≤cash
  origin: ∃π:(P₁).activities.Moves A.s A.o,
    q=stretch (-c/(((C₀).S.a f:ℂ)^d)) (audition (z:=(A.s,A.b)) π A.z)
  field:∀U,q.density A.o ((C₀).localSection d) (P₁) U =
    c*((P₁).eval U:ℂ)*(WilsonReflectedOriginalTwoDeposit.held R (source R A (begin.trans live)) f U-
      WilsonReflectedRestartedPair.mean R N (cropped R A begin) f U)

theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b) (d e:ℕ):
    ∀ᶠ f:ℕ in atTop, ∀N p K, ∀(A:Arm R d N p f K)(begin:f≤K)(live:K≤N), (C₀).ref d≤f →
    ∀(C M:ℝ), 0≤C → 0≤M → Priced R A (C*((β f)^(e+1))⁻¹*((C₀).S.a f)^d*M) →
    ∀c:ℂ, ‖c‖≤1 → ∃ q, Restored R A begin live c
      ((2+orbitCost ((C₀).labels.level d))*C*((β f)^e)⁻¹*M) q :=by
  have rise:Tendsto β atTop atTop:=tendsto_atTop_add_const_left _ _
    (R.alloy.B.a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [WilsonReflectedPublicRotationFare.original R simple shop d,
    WilsonThermometerOffsetLedger.original R simple shop d,rise.eventually_ge_atTop 1]
    with f rotation awake warm N p K A begin live ref C M cp mp stock c small
  let g:=(C₀).S.a f
  let W:=(C₀).path.rep N p f
  let fee:=C*((β f)^(e+1))⁻¹*g^d*M
  let τ:=turnCost W.p.order W.p.power
  let Ω:=orbitCost ((C₀).labels.level d)
  have gp:0<g:=(C₀).S.a_pos f
  have hp:0<β f:=zero_lt_one.trans_le warm
  have τpos:0≤τ:=zero_le_one.trans (one_le_pow₀ (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ one_le_two)))
  have opos:0≤Ω:=zero_le_one.trans (orbitCost_one_le _)
  have tprice:τ≤2*β f:=by
    have r0:τ≤τ*WilsonThermometerOffsetLedger.cash R d f :=le_mul_of_one_le_right τpos awake.2.1
    have inner:0<2+Real.log (β f):=by linarith [Real.log_nonneg warm]
    linarith only [r0,rotation N p (begin.trans live),Real.log_le_sub_one_of_pos inner,
      Real.log_le_sub_one_of_pos hp,warm]
  obtain ⟨q,origin,form,paid,priority,field⟩:=WilsonReflectedPublicSignedCoefficient.original
    R A begin live ref stock c
  have unit:‖-c/((g:ℂ)^d)‖=‖c‖*(g^d)⁻¹:=by
    rw [norm_div,norm_neg,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos gp,div_eq_mul_inv]
  have take (x:ℝ)(xp:0≤x):‖-c/((g:ℂ)^d)‖*(x*fee)≤ x*C*((β f)^(e+1))⁻¹*M:=by
    have eq:‖-c/((g:ℂ)^d)‖*(x*fee)=‖c‖*(x*C*((β f)^(e+1))⁻¹*M):=by
      rw [unit];dsimp [fee]; field_simp [gp.ne']
    rw [eq];apply mul_le_of_le_one_left _ small
    positivity
  have period:((β f)^(e+1))⁻¹ ≤ ((β f)^e)⁻¹ :=by
    exact inv_anti₀ (pow_pos hp e) (pow_le_pow_right₀ warm (Nat.le_succ e))
  have cash:‖-c/((g:ℂ)^d)‖*(τ*fee) ≤ (2+Ω)*C*((β f)^e)⁻¹*M :=calc
    _ ≤ τ*C*((β f)^(e+1))⁻¹*M :=take τ τpos
    _ ≤ (2*(β f))*C*((β f)^(e+1))⁻¹*M := by gcongr
    _ = 2*C*((β f)^e)⁻¹*M :=by rw [pow_succ]; field_simp [hp.ne']
    _ ≤ _ :=by gcongr; linarith only [opos]
  have head:‖-c/((g:ℂ)^d)‖*(Ω*fee) ≤ (2+Ω)*C*((β f)^e)⁻¹*M :=calc
    _ ≤ Ω*C*((β f)^(e+1))⁻¹*M :=take Ω opos
    _ ≤ (2+Ω)*C*((β f)^e)⁻¹*M :=by gcongr; linarith only [opos]
  exact ⟨q,form,rem_mono paid cash,priority.trans head,origin,field⟩

end YM.Integration.WilsonReflectedPublicSignedFare
end
