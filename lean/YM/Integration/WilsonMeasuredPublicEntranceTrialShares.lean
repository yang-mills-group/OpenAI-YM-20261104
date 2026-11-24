import YM.Integration.WilsonMeasuredPublicEntranceCropRoof
import YM.Integration.WilsonMeasuredPublicEntranceTrialPeerOnset
import YM.Integration.WilsonMeasuredPublicEntranceOrderedPeers
/-! Every marked trial contact in the finite conditional product, with
the full physical and independent peers on the two authentic flat ears. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTrialShares
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac MeasureTheory
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open WheelP AnalyticBridge VerifiedReset PhysicalNext PhysicalNext.Repeat Legato
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedCorridor WilsonThermometerMixedCollarSubpower
open Source Labels WilsonOriginalAlternativeHearing WilsonMeasuredCoefficientTransport
open Pert.Asymptotics WilsonThermometerUnitFilingCoarse
open WilsonMeasuredPublicEntranceOrderedPeers WilsonMeasuredPublicEntrancePeerShares
open WilsonMeasuredPublicEntranceCropClock
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple)
variable {V:Type} [DecidableEq V] [Fintype V] (marks:Marker.Census V)(deg:V → ℕ)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "κ" j:max => LocalComparison.forcedDivisor R.family j

theorem original (pace:WilsonWindowReportingPace.Slow R.kit)(book:WilsonReportLampForecast.Ready R.family.path.levels)
    (n t p:ℕ)(np:0<n)(size:Fintype.card V ≤ n)(C gap e:ℝ)(cp:0 ≤ C)(gp:0 ≤ gap)(ep:0<e):
    ∃start:ℕ,∀ᶠ k:ℕ in atTop,∀(N per m school b:ℕ),let f:=k+1
    ∀(_cut:f ≤ N)(bt:b<f),start ≤ b →
    ∀(_way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (Q:D.Tab R.rolls)(π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀j,Rep G (R.family.side j per)),
    Concourse R.alloy R.kit R.T π Γ m N per school Ψ → TicketP R.alloy R.kit D Q →
    ∀(o:V → Site (R.family.side f per))(q:Bool → ∀i,Coefficient (R.family.labels.level (deg i)) (R.family.side f per))
    (w:V → ℝ)(B:Bool → V → ℝ)(X I:Type)[Countable I](Y:Lamps X I G (Ψ f).p o marks)(x:X),
    let P:=R.family.path.rep N per f
    ((R.family.path.levels.params f).supportExponent=100) → (∀i,0<w i ∧ w i ≤ 1) →
    (∀z i,0 ≤ B z i) → (∀i,R.family.ref (deg i) ≤ f) →
    (∀z i,(q z i).Format (o i) R.family.params P) →
    (∀z i,(q z i).remBound (o i) P (κ f) (B z i)) →
    (∀z v,WilsonSeparatedPrefixCanonicalMounted.salary R deg f per (q z) (B z) v ≤ (H f)^t) →
    (∀v,(w v)⁻¹ ≤ Real.exp (C*span (H f))) →
    Y.Paid w (Ψ f).p.B ((Ψ f).p.supportExponent+2) 1 →
    ((f-b:ℕ):ℝ) ≤ gap*(1+Real.log (H f))^4 → (Ψ b).p.supportExponent ≤ 100 →
    ∀(h:∀i,Coefficient (R.family.labels.level (deg i)) (R.family.side f per))(M:V → ℝ),
    (∀i,(h i).Format (o i) R.family.params (Ψ f)) →
    (∀i,(h i).remBound (o i) (Ψ f) (κ f) (M i)) → (∀i,(h i).x=0) → (∀i,(h i).regular=0) →
    (∀i U,‖(h i).density (o i) (R.family.localSection (deg i)) (Ψ f) U/((Ψ f).eval U:ℂ)‖ ≤ Real.exp (C*span (H f))) →
    (∀i,2*(w i*M i) ≤ Real.exp 1) →
    ∀(u i:ℕ),m ≤ u → u ≤ i → ∀ib:i ≤ b,WilsonSingleHardRadius.first R simple ≤ u →
    ∀(Z:Support (R.family.side b per))(center:Site (R.family.side b per))(l:ℕ),center∈Z → coverNumber (Ψ b).p.B Z ≤ l →
    ∀s:marks.Mode,(∀v∈s.val,sites R o bt.le v∈Z) → ∀chosen∈shares s.val.toList,
    let soft:=fun z=>incidence (N:=N) R deg o (q z)
    let trial:=fun j U=>(Y.log x U).part (marks.fire j)
    ‖reading R (N:=N) (WilsonMeasuredPublicEntranceFlatShares.owned R s.val (soft false) trial (soft true)
      (fun j=>account (h j) (Ψ f)) chosen) i (ib.trans bt.le)‖ ≤
      ((H f)^p)⁻¹+e*(regulatorRun R.family N per f)^p*WilsonMeasuredPublicEntranceCropRoof.roof s l:=by
  let C':=WilsonMeasuredPublicEntranceTrialPeerOnset.wide deg t C
  let cal:=gap+2*capital n p t C'+1
  have posC:0 ≤ C':=cp.trans (le_max_left ..)
  have pos:0 ≤ cal:=by dsimp [cal,capital,limit];positivity
  have load(s:marks.Mode):s.val.card ≤ n:=Finset.card_le_univ s.val |>.trans size
  obtain ⟨start,receive⟩:=WilsonMeasuredPublicEntranceTrialOwnerCoupon.original R simple marks n 4 0 p np load cal e pos ep
  obtain ⟨later,provision⟩:=eventually_atTop.mp (WilsonMeasuredPublicEntranceTrialPeerOnset.original R deg
    simple pace book n t p size C cp)
  obtain ⟨halo,actual⟩:=eventually_atTop.mp (WilsonMeasuredPublicEntranceCropRoof.calendar R simple)
  refine ⟨max start halo,?_⟩
  filter_upwards [receive,eventually_ge_atTop later] with k hired high
  intro N per m school b f cut bt ready way D Q π Γ Ψ course ticket o q w B X I inst Y x P support wp bp ref fit remn cols wage
    lamps room point h M hf hrem hx hr thermal hfee u i mu ui ib early Z center l seat housed s placed a chosen
  have mf:m ≤ f:=mu.trans (ui.trans (ib.trans bt.le))
  have equal:(Ψ f).p=P.p:=(WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course mf cut).1.symm
  let v:=a.atName
  let sel:=fun j=>q (WilsonMeasuredPublicEntranceShareRoster.pick a j) j
  let wage':=fun j=>B (WilsonMeasuredPublicEntranceShareRoster.pick a j) j
  have raw:sel=WilsonMeasuredPublicEntranceOrderedPeers.chosen R deg (q false) (q true) a:=by
    funext j;dsimp only [sel,WilsonMeasuredPublicEntranceOrderedPeers.chosen]
    cases WilsonMeasuredPublicEntranceShareRoster.pick a j <;> rfl
  have spend:∀j,WilsonSeparatedPrefixCanonicalMounted.salary R deg f per sel wage' j ≤ (H f)^t:=
    fun j=>cols (WilsonMeasuredPublicEntranceShareRoster.pick a j) j
  have treasury:=provision f (by dsimp [f];omega) N per m school mf cut π Γ Ψ course support o sel wage' w
    a.after.toFinset (fun j=>bp _ j) wp spend wage
  let U:=C'*span (H f)
  let Vmax:=fee n p t C' (H f)
  obtain ⟨rating,uzero,cash,each,estate,travel⟩:=treasury
  have received:=hired N per m school b cut bt ((le_max_left ..).trans ready) way D Q π Γ Ψ course ticket
    deg o sel w wage' X I Y x a.after.toFinset 1 U Vmax (fun j=>(wp j).1) (fun j=>bp _ j) ref
    (fun j=>fit _ j) (fun j=>remn _ j) (by rw [show P.p.supportExponent=100 from
      (R.makes.wilson.represents N per f cut).vac ▸ support];norm_num) equal lamps uzero
    (zero_le_one.trans cash) (fun j=>(each j).1) (fun j=>(each j).2.1) (fun j=>(each j).2.2)
    estate (travel b gap room)
  have belongs:=WilsonMeasuredPublicEntranceShareRoster.original (K:=ℂ) s.val a chosen 0 0 0
  have hold:=received v s belongs.1 (deg v) (h v) (hf v) (hrem v) (hx v) (hr v) (thermal v)
    ((hfee v).trans (Real.exp_le_exp.mpr cash)) (Real.exp_le_exp.mpr rating)
    u i mu ui ib early Z center seat placed
  let clip:=WilsonMeasuredPublicEntranceCropRate.depth n p (H f) U
  let initial:=WilsonMeasuredPublicEntranceTrialPeerBoard.price (N:=N) R deg o (Ψ f) sel a.after.toFinset w (fun _=>clip) wage' 1
  have before:=WilsonMeasuredPublicEntranceCropRoof.original R bt.le (Ψ b) Z l s w v initial (M v)
    (fun j=>(wp j).1) (fun j=>(wp j).2) point housed (actual b ((le_max_right ..).trans ready))
  have gr:0 ≤ regulatorRun R.family N per f:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have paid:=hold.trans (add_le_add_right (mul_le_mul_of_nonneg_left before (mul_nonneg ep.le (pow_nonneg gr p))) _)
  change ‖reading R (N:=N) (fun W=>account (h v) (Ψ f) W*
    ∏j∈s.val.erase v,WilsonMeasuredPublicEntranceFlatShares.rest R (incidence (N:=N) R deg o (q false))
      (fun j A=>(Y.log x A).part (marks.fire j)) (incidence (N:=N) R deg o (q true)) a j W) i _‖ ≤ _
  simp_rw [WilsonMeasuredPublicEntranceOrderedPeers.field (N:=N) R deg o (q false) (q true) marks (Ψ f) Y x,
    ←raw]
  exact paid

end YM.Integration.WilsonMeasuredPublicEntranceTrialShares
end
