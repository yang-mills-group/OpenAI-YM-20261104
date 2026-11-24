import YM.Integration.WilsonReportHarvestSlabCenteredSale
import YM.Integration.WilsonReportHarvestSlabShiftSelected

/-! One common physical Wilson roster and its actual older centered cubic. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabCenteredSelected
open Function Filter Finset Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station WilsonLimitConstruction
open WilsonCloseCaptureCalendar
open Next.Rank RG12 RG17 Extraction Spec Climb Table Trace.Pilot Pier.Lair SharpGram SharpGram.Lenses OPE.Orbits
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
universe u
variable {G : Gauge} (R : Run G) (simple : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (fund : FundedOriginalProperties.{u} simple δ W)
    (book : OPE.Package R.family R.w (mutt R.family.path.levels R.Q) R.doors)
    (portfolio : Funding R) (slow : WilsonWindowReportingPace.Slow R.kit)

variable {order:Extraction.Order}{table:Table R.family.book}{F:Final R.family order table} (L:Layout F)

variable {J:ℝ→FamilyBasis (C:=R.family) table} {u:Filter (ℕ×ℕ)}
    (B:Mantle F u) (E:OPE.Services R.family order table)
    (paid:Pier.Lair.Present F J) (pegs:Pegs B L)
    (near:∀ᶠ r in trail,R.family.S.a (L.level r) ≤ r ∧
      r ≤ R.family.S.a (L.level r)*R.family.path.levels.clock.hatBeta (L.level r)^2)


open WilsonAllDateHarvestFiledReplay
local notation "C" => R.family

open RG05Readout.Nuclear RG05Readout.Pulse Push.GridApprox

def Bought (K d h p b box:ℕ) (ε η:ℝ) (s:Fin 3→ℕ) (r:ℝ) (w:(v:Fin 3)→(C).label (s v))
    (nm:b+1 ≤ WilsonMeasuredWindow.stop (C).path.levels simple K r):Prop :=
  let m:=WilsonMeasuredWindow.stop (C).path.levels simple K r
  let n:=b+1
  let H:=2*(h+1)+2*(K+1)
  ∀charge:ℝ,1 ≤ charge → ∀ᶠ t:ℕ in atTop,∃mt:m ≤ t,∃nt:n < t,∀per:ℕ,
    let N:=t+1
    let g:=(Real.sqrt ((C).path.rep N per t).beta)⁻¹
    let S:=fun v:Fin 3=>portfolio.basis (s v) (N,per)
    let x:=fun v:Fin 3=>WilsonReportHarvestReadmittedSource.filed L (s v) r (w v) (S v) m N per
    ∃P:(v:Fin 3)→Sight C (s v) per,Registered R portfolio L s r w n m N per d H P ∧
      ∀o∈Pulse.area («C»:=R.family) box,2*((C).S.a n*(2*(box:ℝ)+1)) < (C).S.radius per →
      ∀f:Fin 3→Body,(∀i,Tall (f i) (s i+2) 1 1) → Pulse.buy C n per o (r*η/2) f →
        WilsonReportHarvestSlabCenteredSale.Closed R nm mt nt s S P x o f (ε*g^p/charge)

include W fund book slow B pegs near in
theorem chosen (K d box:ℕ)(hk:5 ≤ K){η:ℝ}(ep:0 < η)(s:Fin 3→ℕ)(degree:∀i,s i ≤ d)
    (v:(i:Fin 3)→Free C (s i))(h:ℕ)(w:(r:ℝ)→(i:Fin 3)→(C).label (s i))
    (elected:∀ᶠr in trail,WilsonReportHarvestReplayPrescribed.Selected R L J s v h r (w r))
    (k:ℕ)(warm:∀ᶠn:ℕ in atTop,Warm C n (d+1) k):
    ∀ε:ℝ,0 < ε → ∀p:ℕ,∃b0:ℕ,∀ᶠr in trail,∀b≥b0,
      ∀nm:b+1 ≤ WilsonMeasuredWindow.stop (C).path.levels simple K r,
        Bought R simple portfolio L K d h p b box ε η s r (w r) nm := by
  intro ε hp p
  obtain ⟨B₀,nonneg,h₀,basis⟩:=WilsonReportHarvestSlabSingletonCost.original R s d degree
  obtain ⟨b0,ready⟩:=WilsonReportHarvestSlabShiftSelected.chosen R simple W fund book portfolio slow L B pegs near
    K d box hk ep s degree v h w elected k warm ε hp p (2*d+3) h₀
  refine ⟨b0,?_⟩
  filter_upwards [ready] with r sale b late nm
  let m:=WilsonMeasuredWindow.stop (C).path.levels simple K r
  let n:=b+1
  let H:=2*(h+1)+2*(K+1)
  let mass:=B₀*((C).S.a n/(C).S.a m)^d*((C).path.levels.clock.hatBeta m)^H
  have pos:0 ≤ mass:=mul_nonneg (mul_nonneg nonneg (pow_nonneg (div_nonneg ((C).S.a_pos _).le ((C).S.a_pos _).le) _))
    (pow_nonneg (zero_le_one.trans ((C).path.levels.fits.delayed m).le) _)
  have rate:0≤WilsonPositionSeparatedProfileStableReturn.price:=
    div_nonneg WilsonPositionSeparatedProfileStableStep.shrink_pos.le (sub_pos.mpr WilsonPositionSeparatedProfileStableStep.shrink_lt).le
  let boost:=(1+6*mass)*(1+WilsonPositionSeparatedProfileStableReturn.price)
  have past:1≤boost:=one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  unfold Bought
  intro m' n' H' charge bill
  have space:=sale b late nm (charge*boost) (one_le_mul_of_one_le_of_one_le bill past)
  filter_upwards [space] with t current
  obtain ⟨mt,nt,bank⟩:=current
  refine ⟨mt,nt,?_⟩
  intro per N g S x
  obtain ⟨P,registered,fields⟩:=bank per
  refine ⟨P,registered,?_⟩
  intro o member room f tall buy
  let extra:=WilsonAllDateHarvestFixedSpectatorInvoice.extra R m t (2*d+3) h₀
  have temporal:1≤(C).S.a m/(C).S.a N:=(one_le_div ((C).S.a_pos _)).2 ((C).S.strictAnti.antitone (mt.trans t.le_succ))
  have extra₁:1≤extra:=one_le_mul_of_one_le_of_one_le (one_le_pow₀ temporal) (one_le_pow₀ ((C).path.levels.fits.delayed N).le)
  have cap(i:Fin 3):Cap (s i+2) (f i) 1:=by
    intro j hj u _
    simpa only [one_pow,one_mul] using tall i j hj u
  have receipt:=WilsonReportHarvestSlabCenteredHeld.original R nm mt nt t.le_succ s S P x o (fun _=>(1,false))
    (fun z=>f z.val.1) book (fields o member room f tall buy)
  apply WilsonReportHarvestSlabCenteredSale.original R nm mt nt s S P x o f
    (mul_nonneg hp.le (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)) bill pos extra₁ _ receipt
  intro u _ age i
  change ‖-actualTransport C (N:=N) (Records.clinic C per N (s i) (Many.point (S i) (x i) m N) n (o i) (1,false) (f i)) _ 1‖≤_
  rw [norm_neg]
  exact (basis n m t per H nm mt S P x portfolio.allowance registered.1 (fun i=>(registered.2 i).1)
    i (o i) (f i) (cap i)).2 u _ _

include W fund book slow B E paid pegs near in
theorem original (K d:ℕ)(hk:5 ≤ K)(s:Fin 3→ℕ)(degree:∀i,s i ≤ d)(v:(i:Fin 3)→Free C (s i)):
    ∃(h:ℕ)(w:(r:ℝ)→(i:Fin 3)→(C).label (s i)),
      (∀ᶠr in trail,WilsonReportHarvestReplayPrescribed.Selected R L J s v h r (w r)) ∧
      ∀box:ℕ,∀η:ℝ,0 < η → ∀ε:ℝ,0 < ε → ∀p:ℕ,∃b0:ℕ,∀ᶠr in trail,∀b≥b0,
        ∀nm:b+1 ≤ WilsonMeasuredWindow.stop (C).path.levels simple K r,
          Bought R simple portfolio L K d h p b box ε η s r (w r) nm := by
  obtain ⟨h,w,elected,_⟩:=WilsonReportHarvestReplayPrescribed.original R simple W fund book portfolio slow L B E
    paid pegs near K d (by omega) s degree v
  obtain ⟨k,warm⟩:=(portfolio.dates 0 0 d 0).2
  exact ⟨h,w,elected,fun box _ ep=>chosen R simple W fund book portfolio slow L B pegs near K d box hk ep
    s degree v h w elected k warm⟩

end YM.Integration.WilsonReportHarvestSlabCenteredSelected
