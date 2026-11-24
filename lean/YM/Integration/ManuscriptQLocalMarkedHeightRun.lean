import YM.Integration.ManuscriptQLocalMarkedHeightTail
import YM.Integration.ManuscriptQLocalVacuumCash
import YM.Integration.ManuscriptQLocalMarkedRoster
import YM.Integration.LocalComparisonFullPreparation

/-! Complete rooted high-height terms on one actual endowed marked carrier. The
measured calibration at the original field remains explicit in the incoming law. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalMarkedHeightRun
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy
open MergeProof LocalLTE
open scoped Topology BigOperators Classical

variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Marker.Census V}
  (R:Run G) {J:Request V} (A:NumericSchedule R.family J)
  (d:LocalFormal.Datum R.family Γ) (F:AnalyticInput J A d)
  {η:ℝ} (I:FullPreparedInputAt F η)

abbrev length (J : Request V) := ManuscriptQLocalMarkedHeightTail.horizon J.order (Fintype.card V)

def acquisition (G:Gauge) (J:Request V) :=
  ManuscriptQLocalMarkedHeight.decal G J.outputFieldOrder J.outputDistanceOrder (length J)

local notation "g₁" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "inlet" => QLocalInheritedPhysicalInlet.rep I
local notation "Yᵥ" => ManuscriptQLocalVacuumFamily.source (inlet) F.layers g₁ 1
local notation "LE" => R.alloy.B.a
local notation "j₀" => (LE).clock.J d.level
local notation "j₁" => (LE).clock.J (d.level+1)
local notation "x₀" => (LE).clock.hatBeta d.level
local notation "S₀" => (LE).clock.op d.level d.period
local notation "T₀" => ships R.alloy.B d.cutoff d.level d.period
local notation "Q₀" => R.kit.target j₁ j₀
local notation "ρ₀" => I.inherited+ManuscriptQLocalVacuumRadius.bill F.vacuum.packets g₁ 1

/-- All sources agree at each original field, before true Haar or Gaussian integration.
The finite intermediate calibration is the actually submitted one. -/
theorem material (hi:Retained.NativeIntake I) (x:TestSpace J.tests)
    (U:Config G (R.family.side (d.level+1) d.period)) :
    (I.input.leaf x).density U=(Real.exp (-I.calibration.amount U):ℂ) •
      (Poly.pass (F.packets.read x g₁ U) *
        ((QLocalInheritedRegularSlots.marked (Yᵥ) (ManuscriptQLocalVacuumFamily.carry
          (inlet) F.layers g₁ 1 (QLocalInheritedPhysicalInlet.carried I I.prepared.remainder))).leaf x).density U) := by
  rw [QLocalInheritedRegularSlots.full]
  exact ManuscriptQLocalVacuumFamily.measured I hi x U

section Certificate
variable {c f L:Side} {S:StepData c f} {T:Tube G S} {Y:Rep G f}
  {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W b μ x:ℝ} {o:Target.Order G W}
  (E:Q.Expense) (H:Cash W x μ L Q o b T Y)

def High (J:Request V) (Γ:Marker.Census V) (price:ℝ) : Prop :=
  ∃A b C' d rv s z B e q:ℝ,∃k:ℕ,∃N:Captain H J.outputFieldOrder C' d rv s A b z B e k Chi.canonical,
    ManuscriptQLocalHeightPaidRows.Ready J.outputFieldOrder d B k ∧
    HostQ H N.conduit A B k ∧ Bikes Q L μ x E.earn q B J.outputFieldOrder k ∧
    (1≤betaF G x L ∧ Height.grow G L x^(length J)≤Real.exp (Q.mark L μ x) ∧
      Height.grow G L x^(length J)≤Real.exp (Q.ε*Pressure.Stores.till x) ∧
      ((betaF G x L)^2)^(Fintype.card V)*(Height.grow G L x^(length J))⁻¹≤price) ∧
    ∀(ι:Type)[Fintype ι] (M:ι→Menu.Hat Γ Y) (origin:V→Site f) (w:V→ℝ) (b':ℝ),
    (∀v,0<w v) → Menu.Offer origin M w Y.p.B Y.p.supportExponent b' →
    (Fintype.card V:ℝ)*b'≤betaF G x L →
    Ac.Hit (Captain.reachability (H:=H)) (radiusB x)
      (fun z=>Height.beaconN H (length J) z*Height.rocket H (fun _=>1) z*
        Height.markU N (fun i=>(M i).M) (fun i=>(betaF G x L)^(-(2:ℝ))*Menu.sumFee (M i) w)
          z J.outputDistanceOrder) E.earn 1 ∧
    Ac.Hit (fun z:Fan.Stars H (fun i=>(M i).M)=>Captain.reachability z.1) (radiusB x)
      (fun z=>if Height.tiredN H (length J) z.1 then
        Poly.price w (ManuscriptQLocalMarkedHeightTail.matrix H M z)*
          Captain.wife N z.1 (fun i=>(M i).M) z.2 J.outputDistanceOrder else 0) E.earn price

theorem certificate (J:Request V) (Γ:Marker.Census V) {i:ℕ} {h:Stage}
    (ticket:ManuscriptQLocalMarkedHeight.Booked J.outputFieldOrder J.outputDistanceOrder (length J)
      P Q E L W μ o h i x)
    (works:Works P L x S T) (stamp:ConnectedActivityE6.SliceRows.Stamp T) (cap:Y.activities.EBound Y.p (incomingE G L x))
    (c₀:ℝ) (hp:(betaF G x L)^(-((J.order:ℝ)+1)/2)≤c₀) :
    High E H J Γ c₀ := by
  obtain ⟨A,b,C',d,r,s,z,B,e,q,k,N,ready,hN,hB,bought⟩:=
    ManuscriptQLocalMarkedHeight.genuine H J.outputFieldOrder J.outputDistanceOrder (length J)
      ticket works stamp cap
  have restored:= (ManuscriptQLocalMarkedHeightTail.billed _ ticket.1 J.order (Fintype.card V)).trans hp
  refine ⟨A,b,C',d,r,s,z,B,e,q,k,N,ready,hN,hB,
    ⟨ticket.1,ticket.2.1,ticket.2.2.1,restored⟩,?_⟩
  intro ι _ M origin w b' hw offer bill
  have H₁:=bought V ι Γ M origin w b' hw offer bill
  refine ⟨H₁,fun site=>?_⟩
  have H₂:=ManuscriptQLocalMarkedHeightTail.signed H M N J.outputDistanceOrder (length J)
    w hw ticket.1 ticket.2.1 ticket.2.2.1 H₁
  apply Push.AbsoluteSums.budget_loosen (H₂ site)
  rw [mul_one]
  exact restored

end Certificate

variable (extra:Stage→ℕ→ℝ) (γ:ℝ) (paid:QLocalRequestedSectorCalendar.Paid J (acquisition G J) extra γ R.kit)

theorem original (hG:G.Simple) :
    ∀ᶠ m in (atTop:Filter ℕ),∀(d:LocalFormal.Datum R.family Γ),d.level=m →
      ∀(F:AnalyticInput J A d) {η:ℝ} (I:FullPreparedInputAt F η),Retained.NativeIntake I →
      let lev:=R.alloy.B.a
      let i:=lev.clock.J d.level
      let j:=lev.clock.J (d.level+1)
      let book:=paid.choose j i
      let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
      let Y:=QLocalInheritedRegularSlots.carrier (ManuscriptQLocalVacuumFamily.source
        (QLocalInheritedPhysicalInlet.rep I) F.layers g 1)
      ∃H:Cash book.W (lev.clock.hatBeta d.level) book.μ (lev.clock.op d.level d.period).patch.L
        (target J (R.kit.target j i)) book.order book.c (ships R.alloy.B d.cutoff d.level d.period) Y,
        Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧
          Crossed J γ R A d book H (I.inherited+ManuscriptQLocalVacuumRadius.bill F.vacuum.packets g 1) ∧
          High (expense J (R.kit.target j i)) H J Γ ((2*g)^(J.order+1)) := by
  have h₀:=(tendsto_add_atTop_nat 1).eventually (QLocalRequestedSectorIntake.affordable (J:=J) R hG)
  filter_upwards [ManuscriptQLocalVacuumCash.funds (Γ:=Γ) R A hG,h₀] with m charge money d hm F η I hi
  subst m
  let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
  let old:=ManuscriptQLocalVacuumFamily.source (QLocalInheritedPhysicalInlet.rep I) F.layers g 1
  let Y:=QLocalInheritedRegularSlots.carrier old
  let Δ:=acquisition G J
  let S:=R.alloy.B.a.clock.op d.level d.period
  let T:=ships R.alloy.B d.cutoff d.level d.period
  let x:=R.alloy.B.a.clock.hatBeta d.level
  let β:=betaF G x S.patch.L
  have row:=ManuscriptQLocalVacuumFamily.bought I hi 1
  have hin:=QLocalRequestedSectorIntake.intake R I hi
    (I.inherited_bound.trans (money d.cutoff d.period d.below))
  have e:=ManuscriptQLocalVacuumCash.intake R A d F I hi hin (charge d rfl F I)
  have orig:=QLocalInheritedRegularSlots.intake old e
  have full:=(QLocalInheritedRegularSlots.original old).Ebound row.1.boundE
  obtain ⟨H,ren,cross⟩:=QLocalRequestedSectorCalendar.source_for_on (J:=J) (Δ:=Δ)
    (extra:=extra) (γ:=γ) (R:=R) (paid:=paid) (A:=A) (z:=d) Y orig rfl rfl _ full
  have win:=QLocalRequestedSectorCalendar.selected J Δ extra γ R paid d
  have works:Works _ S.patch.L x S T:=⟨orig.ready,rfl,by rw [add_comm 1];exact R.alloy.B.a.fits.sizeT _ _⟩
  have stamp:=protocol (n:=d.period) R.alloy.B d.below R.kit.pledging.conducts.full
  refine ⟨H,ren,cross,certificate _ H J Γ (i:=S.patch.J)
    (h:=(teller J (query R.metals.p R.metals.K (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level))).below) win.analytic works stamp orig.cap.labels.boundE _ ?_⟩
  have hb:R.alloy.B.a.clock.hatBeta (d.level+1)=β:=Application.clock_next R.alloy.B.a d.level d.period
  have hp:0<β:=zero_lt_one.trans_le win.analytic.1
  have hh:(Real.sqrt β)⁻¹≤2*g:=by
    rw [←hb]
    exact (IterationFour.Currency.hat_g R.makes d.cutoff d.period (d.level+1) d.below).1
  have hpow:(Real.sqrt β)⁻¹=β^(-(1/2:ℝ)):=by rw [Real.rpow_neg hp.le,Real.sqrt_eq_rpow]
  calc
    β^(-((J.order:ℝ)+1)/2)=((Real.sqrt β)⁻¹)^(J.order+1):=by
      rw [hpow,←Real.rpow_natCast,←Real.rpow_mul hp.le]
      congr 1
      push_cast
      ring
    _ ≤ _:=pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg β)) hh _


section SubmittedRoster
variable {R} {A} {d} {F}

/-- Complete relative budget of the submitted independent tests on the actual
vacuum-layer carrier. The same normalized source and all compulsory kernels
enter both the menu and the physical reweight. -/
def rosterBudget :=
  ManuscriptQLocalVacuumFamily.budget (QLocalInheritedPhysicalInlet.rep I) F.layers g₁ 1 _
    (QLocalInheritedPhysicalInlet.remainder I).budget

def rosterBill := 2*((Fintype.card V:ℝ)*I.regularPrice+
  Fintype.card V*(forcedDivisor R.family (d.level+1)*I.forcedPrice))

/-- The full physical-radius offer is already paid by the owner of the
submitted remainder, for all tests and all finite selections of its real
ordinary and compulsory partners. -/
theorem enrolled (base x:IndependentTests J.tests) (E:Finset ℕ) (K:Finset (ℕ×ℕ)) :
    Menu.Offer F.fineRoots (ManuscriptQLocalMarkedRoster.promised (rosterBudget I) base x E K).terms
      F.inputRadii (Yᵥ).p.B (Yᵥ).p.supportExponent (rosterBill I) :=
  ManuscriptQLocalMarkedRoster.offer (rosterBudget I) base x E K

end SubmittedRoster

/-- The true exceptional component debit is uniform over every submitted
intake on this run, including its independent mark radii before all tests. -/
theorem reserve (hG:G.Simple) :
    ∀ᶠ m in (atTop:Filter ℕ),∀(d:LocalFormal.Datum R.family Γ),d.level=m →
      ∀(F:AnalyticInput J A d) {η:ℝ} (I:FullPreparedInputAt F η),Retained.NativeIntake I →
       (Fintype.card V:ℝ)*rosterBill I ≤
         betaF G (R.alloy.B.a.clock.hatBeta d.level) (R.alloy.B.a.clock.op d.level d.period).patch.L := by
  let v:ℝ:=Fintype.card V
  let D:=R.family.path.levels
  have hdiv:Tendsto D.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _
    (D.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))
  have hh:=((hdiv.comp (tendsto_add_atTop_nat 1)).eventually (eventually_ge_atTop (2*v*(v+1))))
  have hf:=LocalComparison.Global.eventually_retained_forced_smallness (V:=V) R.family hG J.forcedConstant
  filter_upwards [hh,hf] with m large force d hm F η I hi
  subst m
  rw [←Application.clock_next]
  have hv:0≤v:=Nat.cast_nonneg _
  have df:=force I.forcedPrice I.forced_bound
  have nonneg:0≤D.clock.forcedAllowance (d.level+1):=(Real.exp_pos _).le
  have hor:v*I.regularPrice≤v:=mul_le_of_le_one_right hv hi.ordinary_small
  have hard:v*(forcedDivisor R.family (d.level+1)*I.forcedPrice)≤1:=by linarith [df]
  calc
    v*rosterBill I=2*v*(v*I.regularPrice+v*(forcedDivisor R.family (d.level+1)*I.forcedPrice)):=by
      unfold rosterBill
      dsimp [v]
      ring
    _ ≤ 2*v*(v+1):=mul_le_mul_of_nonneg_left (add_le_add hor hard) (by positivity)
    _ ≤ _:=large

/-- One original secured sector and one connected estimate serve the entire
submitted signed roster at the original fine-step radii. -/
theorem issued (hG:G.Simple) :
    ∀ᶠ m in (atTop:Filter ℕ),∀(d:LocalFormal.Datum R.family Γ),d.level=m →
      ∀(F:AnalyticInput J A d) {η:ℝ} (I:FullPreparedInputAt F η),Retained.NativeIntake I →
      let lev:=R.alloy.B.a
      let i:=lev.clock.J d.level
      let j:=lev.clock.J (d.level+1)
      let book:=paid.choose j i
      let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
      let Y:=QLocalInheritedRegularSlots.carrier (ManuscriptQLocalVacuumFamily.source
        (QLocalInheritedPhysicalInlet.rep I) F.layers g 1)
      ∃H:Cash book.W (lev.clock.hatBeta d.level) book.μ (lev.clock.op d.level d.period).patch.L
        (target J (R.kit.target j i)) book.order book.c (ships R.alloy.B d.cutoff d.level d.period) Y,
        Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧
          Crossed J γ R A d book H (I.inherited+ManuscriptQLocalVacuumRadius.bill F.vacuum.packets g 1) ∧
          High (expense J (R.kit.target j i)) H J Γ ((2*g)^(J.order+1)) ∧
          (∀(a x:IndependentTests J.tests) (E:Finset ℕ) (K:Finset (ℕ×ℕ)),
            Menu.Offer F.fineRoots (ManuscriptQLocalMarkedRoster.promised (rosterBudget I) a x E K).terms
              F.inputRadii Y.p.B Y.p.supportExponent (rosterBill I)) ∧
          (Fintype.card V:ℝ)*rosterBill I≤betaF G (lev.clock.hatBeta d.level) (lev.clock.op d.level d.period).patch.L := by
  filter_upwards [original (Γ:=Γ) R A extra γ paid hG,reserve (Γ:=Γ) R A hG] with m source fee d hm F η I hi
  obtain ⟨H,hH,win,sold⟩:=source d hm F I hi
  exact ⟨H,hH,win,sold,enrolled I,fee d hm F I hi⟩

end YM.Integration.ManuscriptQLocalMarkedHeightRun
