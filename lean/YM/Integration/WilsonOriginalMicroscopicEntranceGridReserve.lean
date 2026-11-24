import YM.Integration.WilsonReflectedOpticalArm

/-! The scalar reserve for the actual already selected grid landing,
independent of the index presentation of its signed forced stock. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceGridReserve

open Push Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open WilsonReflectedFullPanel WilsonOriginalMicroscopicGuardedPage WilsonOriginalMicroscopicGuardedReporters
open WilsonReflectedFundedHearing WilsonReflectedAffordableArm WilsonInvariantActionPosition
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C₀" => R.family
local notation "L₀" => (C₀).path.levels
local notation "a₀" => (C₀).S.a
local notation "H₀" => (L₀).clock.hatBeta

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (q B cap d:ℕ)(rank:d≤cap){η:ℝ}(room:0<η):
    ∃C:ℝ,0<C ∧ ∃floor:ℕ,∀j,floor≤j→∀f (_:j≤f),
    a₀ j/a₀ f≤(H₀ f)^B → ((L₀).budget j).supportExponent≤100 →
    ((L₀).budget f).supportExponent≤100 →
    let t:=WilsonReflectedOpticalRate.depth (q+2) B cap
    let K:=berth R t f
    ∃_:f<K,(H₀ f)^t≤a₀ f/a₀ K ∧ a₀ f/a₀ K≤(H₀ f)^t*(H₀ f)^η ∧
    ∀(v:(C₀).label d)(V:ℝ),0≤V →
      ((C₀).labels.level d).coeffSize v ≤ WilsonOriginalMicroscopicGuardedReporters.stretch R (1/32) j K*
        ((1+wrapCost R d j)*((a₀ j)^d*V)) →
      charge R d f*(hike (C₀) K f rate*((1+4*stock (C₀) K)*((C₀).labels.level d).coeffSize v))
        ≤ C*((H₀ f)^q)⁻¹*(a₀ f)^d*V:=by
  obtain ⟨c,cp,funded⟩:=WilsonReflectedOpticalStock.original R simple slow d
  obtain ⟨F,finance⟩:=eventually_atTop.mp funded
  obtain ⟨E,date⟩:=eventually_atTop.mp (WilsonReflectedOpticalRate.original R simple slow (q+2) B cap room)
  refine ⟨4*c,by positivity,max F E,?_⟩
  intro j start f early close αj αf
  let K:=berth R (WilsonReflectedOpticalRate.depth (q+2) B cap) f
  have window:=date f (((le_max_right ..).trans start).trans early)
  have late:f<K:=window.1
  refine ⟨late,window.2.1,window.2.2.1,?_⟩
  intro v V vp filed
  have posW:0≤1+wrapCost R d j:=by
    have w:0 ≤ WilsonCapturedPrimaryCoreBill.wrapFee ((C₀).labels.level d) (C₀).params:=
      mul_nonneg (Nat.cast_nonneg _) (germ_close ((C₀).labels.level d) (C₀).params).choose_spec.1.le
    exact add_nonneg zero_le_one (mul_nonneg (mul_nonneg w (Real.exp_nonneg _)) (zero_le_one.trans ((L₀).params _).columns_ge))
  let h:=hike (C₀) K f rate
  let k:=1+4*stock (C₀) K
  let s':=WilsonOriginalMicroscopicGuardedReporters.stretch R (1/32) j K
  let u:=1+wrapCost R d j
  let z:=charge R d f
  have hp:0≤h:=Real.rpow_nonneg (div_nonneg ((C₀).S.a_pos K).le ((C₀).S.a_pos f).le) _
  have ks:0≤ stock (C₀) K:=zero_le_one.trans ((L₀).params K).columns_ge
  have kp:0≤k:=by dsimp only [k];linarith only [ks]
  have sp:0≤ s':=by unfold s' WilsonOriginalMicroscopicGuardedReporters.stretch;positivity
  have zp:0≤z:=by
    have st:0≤ stock (C₀) f:=zero_le_one.trans ((L₀).params f).columns_ge
    have pr:0≤projectionBill R d f:=mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
    unfold z charge;linarith only [st,pr]
  have field:h*(k*((C₀).labels.level d).coeffSize v)≤h*(k*(s'*(u*((a₀ j)^d*V)))):=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left filed kp) hp
  have root:=finance j ((le_max_left ..).trans start) f early αj αf
  have fr:0<(a₀ f)^d:=pow_pos ((C₀).S.a_pos f) _
  have one:1≤a₀ j/a₀ f:=(one_le_div ((C₀).S.a_pos f)).mpr ((C₀).S.strictAnti.antitone early)
  have small:(a₀ j/a₀ f)^d*h*k*s'≤4*((H₀ f)^(q+2))⁻¹:=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ one rank) hp) kp) sp).trans (window.2.2.2 j close)
  have Hp:0<H₀ f:=zero_lt_one.trans ((L₀).fits.delayed f)
  have balance:4*((H₀ f)^(q+2))⁻¹*(c*(H₀ f)^2)=4*c*((H₀ f)^q)⁻¹:=by
    rw [pow_add];field_simp [Hp.ne']
  calc
    z*(h*(k*((C₀).labels.level d).coeffSize v)) ≤ z*(h*(k*(s'*(u*((a₀ j)^d*V))))):=mul_le_mul_of_nonneg_left field zp
    _ = ((a₀ j/a₀ f)^d*h*k*s')*(z*u)*(a₀ f)^d*V:=by rw [div_pow];field_simp [fr.ne']
    _ ≤ (4*((H₀ f)^(q+2))⁻¹*(c*(H₀ f)^2))*(a₀ f)^d*V:=by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul small root (mul_nonneg zp posW) (mul_nonneg (by norm_num) (inv_nonneg.mpr (pow_nonneg Hp.le _)))) fr.le) vp
    _ = _ :=by rw [balance]

end YM.Integration.WilsonOriginalMicroscopicEntranceGridReserve
end
