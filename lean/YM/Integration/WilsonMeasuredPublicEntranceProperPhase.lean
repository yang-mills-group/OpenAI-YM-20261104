import YM.Integration.WilsonMeasuredPublicEntranceCutoffHearing
import YM.Integration.WilsonOriginalTwoFlatGridScaling
import YM.Integration.WilsonAddressedPublicGridRooms
import YM.Integration.WilsonSeparatedPrefixCellProfile
/-! The true returned N-word and the independently measured K-word are heard at the same original ear before a signed smooth position sum. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceProperPhase
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
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n→ℕ)
local notation "C₀" => R.family

theorem word_at {N per f:ℕ}(live:f≤N)(s:(Stock.census (Fin n)).Mode)
    (o:Fin n→ Cover)(Y:∀v,(C₀).label (d v))(turn:Fin n→Motion):
    physical R d (N:=N) Y turn (fun v=>wrap ((C₀).side f per) (o v)) s=
      word R (fun v:↥s.val=>d v.val) f N per live (fun v=>o v.val)
        (fun v=>displayed R (d v.val) (Y v.val) (turn v.val)):=by
  funext U
  unfold physical word
  simp_rw [WilsonAddressedPublicGridRooms.top R live]
  let X:=fun v:Fin n=>(C₀).O N per (displayed R (d v) (Y v) (turn v)) (((C₀).S.toDepth live per).embed (wrap ((C₀).side f per) (o v))) U
  exact (Finset.prod_coe_sort s.val X).symm

theorem actual {N per u:ℕ}(road:u≤N)(raw:Config G ((C₀).side N per)→ℂ):
    gap R N per u road raw=(C₀).omega N per raw-actualTransport (C₀) (N:=N) raw road 1:=by
  unfold gap WilsonThermometerUnitFilingCoarse.reading
  rw [gust_base,←WilsonSeparatedOriginalSlabHeldProxy.normalized R road raw]
  ring

theorem original {r W pupil}(L:Package (C₀) W r pupil)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    {J u:ℕ}(stop:Stop (C₀) 0 J u)(s:(Stock.census (Fin n)).Mode)(active:s.val.Nonempty)(B q:ℕ):
    ∀ᶠ f:ℕ in atTop,∀t:ℝ,0<t→t≤(C₀).S.a (u+3)→(C₀).S.a f<t→t≤((C₀).path.levels.clock.hatBeta f)^B*(C₀).S.a f→
    ∀N per (deep:f<N)(o:Fin n→ Cover),
    (∀v:↥s.val,8*‖(C₀).S.gridPoint f (o v.val)‖≤t) →
    (Pairwise fun v w:↥s.val=>2*(C₀).S.a f*(((C₀).path.levels.budget f).B:ℝ)^2≤
      ‖(C₀).S.gridPoint f (o v.val)-(C₀).S.gridPoint f (o w.val)‖) →
    ∀(Y:∀v,(C₀).label (d v))(turn:Fin n→Motion)(fare:↥s.val→ℝ),(∀v,0<fare v) →
    (∀v:↥s.val,Spindle.paid (C₀) (d v.val) f N per (displayed R (d v.val) (Y v.val) (turn v.val))≤fare v) →
    ∀road:u≤f,let raw:=physical R d (N:=N) Y turn (fun v=>wrap ((C₀).side f per) (o v)) s
    ‖(C₀).omega N per raw-actualTransport (C₀) (N:=N) raw (road.trans deep.le) 1‖≤
      (∏v,fare v)*(((C₀).path.levels.clock.hatBeta f)^q)⁻¹:=by
  classical
  letI:Nonempty ↥s.val:=⟨⟨active.choose,active.choose_spec⟩⟩
  filter_upwards [WilsonOriginalTwoFlatGridScaling.original R (fun v:↥s.val=>d v.val) L simple slow stop B q] with f paid
  intro t tp small finer span N per deep o inside away Y turn fare positive enrolled road raw
  have sale:=paid tp small finer span N per deep (fun v:↥s.val=>o v.val) inside away
    (fun v=>displayed R (d v.val) (Y v.val) (turn v.val)) fare positive enrolled road
  rw [←word_at R d deep.le s o Y turn,actual] at sale
  exact sale

end YM.Integration.WilsonMeasuredPublicEntranceProperPhase
end
