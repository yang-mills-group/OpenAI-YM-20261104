import YM.Integration.WilsonMeasuredPublicEntranceCutoffHearing
import YM.Integration.WilsonMeasuredPublicEntranceProperPhase
import YM.Integration.WilsonMeasuredPublicEntranceJointBilled
import YM.Integration.WilsonSeparatedPrefixCellProfile
/-! The true returned N-word and the independently measured K-word are heard at the same original ear before a signed smooth position sum. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceGibbsProfile
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open PhysicalNext.Repeat.Legato RG16 RG16.Literal WilsonThermometerUnitFilingCoarse
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonThermometerReflectedTrajectory (anchorAt)
open WilsonReflectedPublicOrientedFaces (displayed)
open WilsonMovingForkMixedSeed WilsonAddressedFiniteGuardTrial WilsonPositionProgramReportedField
open WilsonMeasuredPublicEntrancePanel (Panel Reading charged)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonPositionProgramBlockedTrialAddBack (uncut)
open WilsonMeasuredPublicEntranceMasterUpper (ReadAt)
open WilsonMeasuredPublicEntranceScreen (Ground)
open PertExtension PertExtension.LatticePT
open scoped Classical BigOperators Topology

open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)
open WilsonMeasuredPublicEntranceCellWords (physical)
open OPE Next.Rank Overlay Bid MergeProof Ribbons Accent ManyCopies Cells
open PhysicalNext.Repeat.Mallow Bandage Next.UVStress

open WilsonAddressedPhysicalCells
open WilsonMeasuredPublicEntranceProfileRegistry (Billed)
open MeasureTheory
variable {k:ℕ}{I:Type}[Fintype I]

theorem add {side:Side}(φ:Test k)(a r:ℝ)(pos:0<a)(D E:Sites side k→ℂ){x y:ℝ}
    (before:Billed φ a r side D x)(after:Billed φ a r side E y):
    Billed φ a r side (fun c=>D c+E c) (x+y):=by
  have eq:=WilsonSeparatedPrefixCellProfile.tested φ a r side pos (fun c=>D c+E c)
  refine ⟨eq,?_⟩
  have heard:φ.applyTo (fun X=>D (atSite a r side X)+E (atSite a r side X))=
      φ.applyTo (fun X=>D (atSite a r side X))+φ.applyTo (fun X=>E (atSite a r side X)):=by
    rw [eq,before.1,after.1]
    simp only [mul_add,Finset.sum_add_distrib]
  rw [heard,mul_add]
  exact (norm_add_le _ _).trans (add_le_add before.2 after.2)

variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n→ℕ)
local notation "C₀" => R.family

theorem original {r W pupil}(L:Package (C₀) W r pupil)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    {J u:ℕ}(stop:Stop (C₀) 0 J u)(s:(Stock.census (Fin n)).Mode)(active:s.val.Nonempty)(B q:ℕ):
    ∀ᶠ f:ℕ in atTop,∀t:ℝ,0<t→t≤(C₀).S.a (u+3)→(C₀).S.a f<t→t≤((C₀).path.levels.clock.hatBeta f)^B*(C₀).S.a f→
    ∀N per (deep:f<N)(φ:Test k)(scale:ℝ)(amp:I→ℂ)(o:I→Sites ((C₀).side f per) k→Fin n→ Cover)
    (Y:I→∀v,(C₀).label (d v))(turn:I→Fin n→Motion)(fare:I→↥s.val→ℝ),(∀b v,0<fare b v) →
    (∀b (v:↥s.val),Spindle.paid (C₀) (d v.val) f N per (displayed R (d v.val) (Y b v.val) (turn b v.val))≤fare b v) →
    (∀b c,mass φ ((C₀).S.a f) scale ((C₀).side f per) c≠0→∀v:↥s.val,8*‖(C₀).S.gridPoint f (o b c v.val)‖≤t) →
    (∀b c,mass φ ((C₀).S.a f) scale ((C₀).side f per) c≠0→Pairwise fun v w:↥s.val=>2*(C₀).S.a f*(((C₀).path.levels.budget f).B:ℝ)^2≤
      ‖(C₀).S.gridPoint f (o b c v.val)-(C₀).S.gridPoint f (o b c w.val)‖) →
    ∀(road:u≤f)(K:ℕ)(ahead:f≤K)(Q:I→Sites ((C₀).side f per) k → Config G ((C₀).side K per)→ℂ)(rate:ℝ),
    let raw:=fun b c=>physical R d (N:=N) (Y b) (turn b) (fun v=>wrap ((C₀).side f per) (o b c v)) s
    let future:=fun b c=>actualTransport (C₀) (N:=K) (Q b c) (road.trans ahead) 1
    let earlier:=fun b c=>actualTransport (C₀) (N:=N) (raw b c) (road.trans deep.le) 1
    Billed φ ((C₀).S.a f) scale ((C₀).side f per) (fun c=>∑b,amp b*(earlier b c-future b c)) rate →
    Billed φ ((C₀).S.a f) scale ((C₀).side f per) (fun c=>∑b,amp b*((C₀).omega N per (raw b c)-future b c))
      ((∑b,‖amp b‖*((∏v,fare b v)*(((C₀).path.levels.clock.hatBeta f)^q)⁻¹))+rate):=by
  classical
  filter_upwards [WilsonMeasuredPublicEntranceProperPhase.original R d L simple slow stop s active B q] with f paid
  intro t tp cap fine clock N per deep φ scale amp o Y turn fare positive enrolled inside apart road K ahead Q rate raw future earlier received
  let edge:=fun b c=>(C₀).omega N per (raw b c)-earlier b c
  let cost:=fun b=>(∏v,fare b v)*(((C₀).path.levels.clock.hatBeta f)^q)⁻¹
  have single(b):Billed φ ((C₀).S.a f) scale ((C₀).side f per) (edge b) (cost b):=by
    refine ⟨WilsonSeparatedPrefixCellProfile.tested _ _ _ _ ((C₀).S.a_pos f) _,?_⟩
    apply WilsonSeparatedPrefixCellProfile.priced _ _ _ _ ((C₀).S.a_pos f) _ (cost b)
    · dsimp [cost]
      exact mul_nonneg (Finset.prod_nonneg fun v _=>(positive b v).le) (inv_nonneg.mpr (pow_nonneg (zero_lt_one.trans (R.alloy.B.a.fits.delayed f)).le _))
    · intro c live
      exact paid t tp cap fine clock N per deep (o b c) (inside b c live) (apart b c live)
        (Y b) (turn b) (fare b) (positive b) (enrolled b) road
  have total:=WilsonMeasuredPublicEntranceJointBilled.original φ ((C₀).S.a f) scale ((C₀).side f per) ((C₀).S.a_pos f) amp edge cost single
  have joined:=add φ ((C₀).S.a f) scale ((C₀).S.a_pos f) _ _ total received
  have combine (c): (∑b,amp b*edge b c)+(∑b,amp b*(earlier b c-future b c))=
      ∑b,amp b*((C₀).omega N per (raw b c)-future b c):=by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    dsimp [edge];ring
  simpa only [combine] using joined

end YM.Integration.WilsonMeasuredPublicEntranceGibbsProfile
end
