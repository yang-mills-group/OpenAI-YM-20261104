import YM.Integration.WilsonReflectedPublicCommonEstate

/-! The original K-site residual for the same measured vector, scaled by
its actual source dose.  The two ends of the interval share the stencil. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicReflectedKColumn
open Push Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open WilsonReflectedFullPanel WilsonOriginalMicroscopicGuardedPage WilsonReflectedFundedHearing WilsonReflectedRestoredStation
open WilsonReflectedPublicGuardedMotion Extra.Multi WilsonReflectedOpticalArm
open Push.Local Planned.GuardedAtom
open private deposited from YM.Integration.WilsonReflectedOpticalArm
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){N p K f d:ℕ}
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "P₀" => (C₀).path.rep N p K
local notation "a₀" => (C₀).S.a K
local notation "Ω" => orbitCost (F₀)
local notation "H" => (C₀).path.levels.clock.hatBeta K

def sourceFee (A:Arm R d N p f K)(c:ℂ):ℝ:=
  (F₀).coeffSize ((c*((a₀:ℂ)^d)⁻¹) • coords R A)

def gross (d K:ℕ):ℝ:=WilsonReflectedAffordableArm.charge R d K*(1+4*GermGraph.stock (C₀) K)*orbitCost ((C₀).labels.level d)

theorem back (A:Arm R d N p f K)(c:ℂ):
    ‖-c/((a₀:ℂ)^d)‖*(F₀).coeffSize A.w≤Ω*sourceFee R A c:=by
  let μ:Motion:=(A.s,A.b)
  have double:Motion.backward (Motion.backward μ)=μ:=by simp [Motion.backward]
  have roundTrip:=Motion.round (F₀) (Motion.backward μ) A.w
  rw [double] at roundTrip
  have bounded:(F₀).coeffSize A.w≤Ω*(F₀).coeffSize (coords R A):=calc
    _=(F₀).coeffSize (Motion.patch (F₀) (Motion.backward μ) (coords R A)):=congrArg _ roundTrip.symm
    _≤_:=Motion.patch_cost (F₀) (Motion.backward μ) (coords R A)
  have same:‖-c/((a₀:ℂ)^d)‖=‖c*((a₀:ℂ)^d)⁻¹‖:=by rw [div_eq_mul_inv,neg_mul,norm_neg]
  rw [same,sourceFee,Size.smul]
  calc
    _ ≤ ‖c*((a₀:ℂ)^d)⁻¹‖*(Ω*(F₀).coeffSize (coords R A)):=mul_le_mul_of_nonneg_left bounded (norm_nonneg _)
    _ = _:=by ring

def Filed (A:Arm R d N p f K)(front:f≤K)(high:K≤N)(c:ℂ)(B:Arm R d N p K K)
    (Q:Coefficient (F₀) ((C₀).side K p))(cash head:ℝ):Prop:=
  Situated R front A B ∧
  (∃π:(P₀).activities.Moves B.s B.o,
     Q=stretch (-c/((a₀:ℂ)^d)) (audition (z:=(B.s,B.b)) π B.z)) ∧
  Q.Format B.o (C₀).params (P₀) ∧ Q.remBound B.o (P₀) (safety (C₀) K) cash ∧
  (F₀).coeffSize Q.x≤head ∧
  ∀U,Q.density B.o ((C₀).localSection d) (P₀) U=c*((P₀).eval U:ℂ)*
    (WilsonReflectedOriginalTwoDeposit.held R (source R A (front.trans high)) K U-cropped R A front U)

theorem original (A:Arm R d N p f K)(front:f≤K)(high:K≤N)(ref:(C₀).ref d≤K)
    (j q:ℕ)(start:j≤K){η bank:ℝ}{M:(C₀).label d ≃ₗ[ℂ] (C₀).label d}
    (bought:WilsonReflectedFullPanel.receipt R d j K N p q start high η M A.Y bank)
    (vector:A.w=M.symm (full R d N p j A.Y))(c:ℂ):
    ∃B:Arm R d N p K K,∃Q:Coefficient (F₀) ((C₀).side K p),
      Filed R A front high c B Q (turnCost (P₀).p.order (P₀).p.power*gross R d K*sourceFee R A c)
        (Ω*gross R d K*sourceFee R A c):=by
  obtain ⟨B,situated,bill⟩:=WilsonReflectedRestoredStation.purchased R front start high A bought vector
  have gp:0<(C₀).S.a K:=(C₀).S.a_pos _
  have st:0≤GermGraph.stock (C₀) K:=zero_le_one.trans ((C₀).path.levels.params K).columns_ge
  have pr:0≤WilsonReflectedAffordableArm.projectionBill R d K:=mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have cp:0≤WilsonReflectedAffordableArm.charge R d K:=by unfold WilsonReflectedAffordableArm.charge;positivity
  have cap:B.cash=(1+4*GermGraph.stock (C₀) K)*(F₀).coeffSize A.w:=by
    simpa only [GermGraph.hike,div_self gp.ne',Real.one_rpow,one_mul] using bill
  have income:0≤B.cash:=by rw [cap];exact mul_nonneg (by positivity) (Work.G08.size_nonneg ..)
  let fee:=WilsonReflectedAffordableArm.charge R d K*B.cash
  have stock₀:Priced R B fee:=deposited R B income le_rfl
  obtain ⟨Q,origin,form,rem,head,field⟩:=WilsonReflectedPublicSignedCoefficient.original R B (le_refl K) high ref stock₀ c
  have unit:‖-c/((a₀:ℂ)^d)‖*fee≤gross R d K*sourceFee R A c:=by
    dsimp only [fee,gross]
    rw [cap]
    calc
      _=(WilsonReflectedAffordableArm.charge R d K*(1+4*GermGraph.stock (C₀) K))*
        (‖-c/((a₀:ℂ)^d)‖*(F₀).coeffSize A.w):=by ring
      _≤_:=by
        rw [mul_assoc (WilsonReflectedAffordableArm.charge R d K*(1+4*GermGraph.stock (C₀) K))]
        exact mul_le_mul_of_nonneg_left (back R A c) (mul_nonneg cp (by positivity))
  have transfer (τ:ℝ)(pos:0≤τ):‖-c/((a₀:ℂ)^d)‖*(τ*fee)≤τ*gross R d K*sourceFee R A c:=by
    calc
      _=τ*(‖-c/((a₀:ℂ)^d)‖*fee):=by ring
      _≤τ*(gross R d K*sourceFee R A c):=mul_le_mul_of_nonneg_left unit pos
      _=_:=by ring
  refine ⟨B,Q,situated,origin,form,rem_mono rem (transfer _ (by unfold turnCost; positivity)),head.trans (transfer _ (zero_le_one.trans (orbitCost_one_le _))),?_⟩
  intro U
  obtain ⟨src,trial⟩:=WilsonReflectedRestoredStation.traded R front high A B situated
  simpa only [src,WilsonReflectedRestartedPair.mean,dif_pos le_rfl,actualTransport_base (C₀) R.makes high,trial] using field U

end YM.Integration.WilsonOriginalPublicReflectedKColumn
