import YM.Integration.WilsonOriginalObservedRosePublicSchool
import YM.Integration.WilsonOriginalObservedRoseSevenScale
import YM.Integration.WilsonOriginalObservedRosePublicGross
import YM.Integration.WilsonOriginalObservedRosePublicMesh

/-! The connected finite Rose through the Haar order and through the earlier optical order on the same funded physical 6/4/4 and the same seven ordinary fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRosePublicConnected
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Shard
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonOlderFreshSoftSocketRestored (stopped coin rated)
open WilsonOlderFreshSoftSocketGross (gross)
open WilsonOlderFreshSoftSocketTotal (normalized)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonOlderFreshSoftSocketFaces (fill)
open WilsonOlderFreshHybridClock (flat)
open WilsonReportingAbsoluteInletForecastBooks (mass value)
open WilsonCoeffUV.Winding
open scoped Topology BigOperators Classical

open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams
open GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare

open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonReflectedPublicStationFare

open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
  {z:Trace.Terrace.Arch R.family}

local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => R.family.path.levels.clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatRoseBook (group)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonOriginalMicroscopicGuardedGridSchool (Finished)
open WilsonOlderFreshSoftRoseMesh (filed)
open WilsonPositionThermometerGradedSource
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations
open WilsonReflectedPublicStationFare
open PhysMS
open MS MS.Land FVA2 FVA2.Register
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse

variable (Jr:ℝ→tower S)(Z:WilsonPrescription G)

open WilsonOriginalObservedRoseVanePurse (ages)
open WilsonOriginalObservedRoseMeshHeight (variation)
open WilsonOriginalMicroscopicGuardedPage (wrapCost)
open Extra.Histories.Motion (orbitCost orbitCost_one_le)
open WilsonOlderFreshSoftSocketStationPair (amount)
open WilsonOriginalObservedRoseMeshHeight (tilt height)
open WilsonOriginalObservedRoseScaledWallet (share)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonReceivedCanonicalVersePortfolio (weight Selection wallet)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonThermometerDeclaredSeeds
local notation "J" => Stock.census (Fin 3)

open WilsonCoeffUV.Bank.Ticket
open WilsonOlderFreshSoftSocketOptical (fixed fixed_nonneg)
open WilsonOriginalObservedRoseStoppedSalary (stop)
local notation "σ" => R.family.S.scale
local notation "g" => Pert.Asymptotics.regulatorRun R.family

open WilsonOriginalOpticalSchedule (prepared)
open WilsonOlderFreshSoftRoseCourse (seat)
open WilsonOlderFreshSoftRoseNodes (Covered)
open WilsonOlderFreshSoftRoseIncome (Stock)
universe u
variable {axis:Axis}{ε:ℝ}{schedule:WilsonOriginalAllOrderCourse.Schedule G}{crop:Campaign R}{W:Campaign.Pillars R crop}

open WilsonOriginalObservedRosePublicMesh (aperture)
open WilsonInvariantActionPosition (berth)

open WilsonOriginalObservedRosePublicGross (base)
open WilsonPositionThermometerConnected (value)
local notation "Faces" => Finset (Fin 3)

private def mark (s:Faces):(J).Mode:=⟨s,Finset.mem_univ _⟩

def cut (target bank debt width:ℕ):ℕ:=
  target+(3*base bank debt+WilsonOriginalObservedRosePublicMesh.aperture width*14)+1

private theorem paid_cut {θ:ℝ}(pos:0<θ)(cash:21≤θ⁻¹)(target bank debt width:ℕ):
    21*(θ⁻¹)^(3*base bank debt+WilsonOriginalObservedRosePublicMesh.aperture width*14)*θ^(cut target bank debt width)≤θ^target:=by
  let n:=3*base bank debt+WilsonOriginalObservedRosePublicMesh.aperture width*14
  have unit:21*θ≤1:=by simpa only [inv_mul_cancel₀ pos.ne'] using mul_le_mul_of_nonneg_right cash pos.le
  have repay:(θ⁻¹)^n*θ^n=1:=by rw [←mul_pow,inv_mul_cancel₀ pos.ne',one_pow]
  calc 21*(θ⁻¹)^n*θ^(target+n+1)=(21*θ)*θ^target*((θ⁻¹)^n*θ^n):=by
         rw [pow_succ θ (target+n),pow_add θ target n]
         ring
       _=(21*θ)*θ^target:=by rw [repay,mul_one]
       _≤θ^target:=mul_le_of_le_one_left (pow_nonneg pos.le _) unit

private theorem mass_on (s:Faces):
    WilsonCoeffUV.Wheel.Mark.mass (WilsonOlderFreshSoftRoseCourse.grade ∘ seat s) Finset.univ=
      WilsonCoeffUV.Wheel.Mark.mass ages s:=by
  change (∑i:s,ages i.val)=∑i∈s,ages i
  exact Finset.sum_coe_sort s _

private theorem restored {L M:Levels G}(h:L=M)(x:Digits M (Fin 3)):
    cast (congrArg (fun q=>Digits q (Fin 3)) h) (show Digits L (Fin 3) from h.symm ▸ x)=x:=by cases h;rfl

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(lead:Leading F Jr)
    (obedient:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    (slow:WilsonWindowReportingPace.Slow R.kit)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (cap:∀j,1≤((P).budget j).supportExponent)(upper:∀j,((P).budget j).supportExponent≤100)
    (quote:OPE.Therm.Poetry (P))
    (funded:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε (prepared schedule) R crop W):
    ∃bank:ℕ,∀target debt width:ℕ,∃U:Set ℝ,U∈trail ∧
    let J₀:=cut target bank debt width
    ∀Q:ℕ,J₀≤Q → ∀L:ℕ,∀D:Fin 3→ℕ,(∀i,ages i<D i) → ∀X opt tol:ℝ,0≤X → 0≤opt → 0<tol →
    ∃start:ℕ,∀ᶠv:ℕ in atTop,∃(V:Realm G (Q+1) Credit.leanC)(draw:V.draws=P),
    V.paid=R.metals.O ∧ V.y=zz P ∧ V.anchor=v ∧ Covered R D Q v start V draw opt tol ∧
    (∀s:Finset (Fin 3),s.Nonempty → Stock R D Q v start V draw opt tol s) ∧
    ∀r∈U,∀{T:ℕ}(B:Book F (l:=l) H z 6 T r),WilsonMovingForkWindowBooks.Priced F B →
    ∀actual:Next.UVStress.Lifts (C) B.k,let K:=berth R width B.W.k
    v≤B.W.k → ∀(N per b c requested power tag:ℕ)(credit:ℝ)(bk:b≤K)(kn:K≤N),b<N →
    v≤c → c≤K → v+1≤K → σ K-σ v≤L*Real.log (β v) →
    let θ:=g N per v
    ∀(file:Filed R ages K)(panel:Panel R ages N per b K bk kn requested power tag credit),
    panel.slot=file.station → panel.axis=file.A N per → (∀i,panel.slot i=B.W.k) →
    (∀i,panel.names i=WilsonNeutralOffsetCutoff.named R (group F Jr Z B actual) N per i) →
    ∀(κ:(i:Fin 3)→Knob (D i))(pt:Fin 3→Chamber)(cells:Digits (P) (Fin 3))(y:Fin 3→ Cover)
      (test:(s:Faces)→Pen D s→L[ℝ]ℝ),(∀s:Faces,s.Nonempty → ‖test s‖≤X*(θ⁻¹)^debt) →
    let w:=votes R ages (N:=N) (per:=per) file panel.names panel.turn
    let row j s:=normalized R ages κ pt N per K c v cells s w y (test s) j θ
    r^14*‖value (row Q)-value (row J₀)‖≤θ^target:=by
  obtain ⟨E,offers⟩:=WilsonOriginalObservedRosePublicGross.original F Jr Z simple bliss lead obedient slow shop cap upper quote
  refine ⟨E,?_⟩
  intro target debt width
  let A:=WilsonOriginalObservedRosePublicMesh.aperture width
  obtain ⟨U,active,calendar⟩:=offers debt A
  refine ⟨U,active,?_⟩
  intro J₀ Q retained L D fits X opt tol xp op tp
  have all:=Filter.eventually_all.mpr (fun s:{s:(J).Mode // s.val.Nonempty}=>calendar Q J₀ retained L D s.val s.property X xp)
  obtain ⟨start,school⟩:=WilsonOlderFreshSoftSocketFigureRoom.original R funded D fits Q opt tol op tp
  refine ⟨start,?_⟩
  filter_upwards [all,school,WilsonOriginalObservedRosePublicMesh.original R simple slow width L,
    WilsonSeparatedPrefixKineticGeometry.spend R simple 21 0] with v rates bought mesh spend
  obtain ⟨V,draw,scheme,heat,anchor,complete,covered,issued⟩:=bought
  refine ⟨V,draw,scheme,heat,anchor,covered,issued,?_⟩
  intro r hr T B book actual K vj N per b c requested power tag credit bk kn deep vc ck next span θ file panel stations axes homes names κ pt cells y test capFee w row
  have top:r/(a K)≤(θ⁻¹)^A:=calc
    _=B.W.wheel.r/(a K):=congrArg (fun x:ℝ=>x/(a K)) B.active.symm
    _≤_:=mesh B.W.k vj B.W.b B.checked.high.2 N per kn span
  have shaped:(a B.W.k)≤r:=(WilsonReflectedPublicBulbBerth.mesh R B.W B.checked).trans B.active.le
  have first: (a B.W.k)/(a K)≤(θ⁻¹)^A:=(div_le_div_of_nonneg_right shaped ((C).S.a_pos K).le).trans top
  let printed:Digits V.draws (Fin 3):=draw.symm ▸ cells
  have same:cast (congrArg (fun q=>Digits q (Fin 3)) draw) printed=cells:=restored draw _
  have enrolled (s:Faces)(hs:s.Nonempty):
      (∀k:ℕ,k≤Q → r^(height ages s)*‖row k s‖≤(θ⁻¹)^(base E debt+A*height ages s)) ∧
      r^(height ages s)*‖row Q s-row J₀ s‖≤(θ⁻¹)^(base E debt+A*height ages s)*θ^J₀:=by
    have entry:=rates (⟨mark s,hs⟩) V draw scheme heat anchor.le (mass_on s ▸ complete s)
      r hr B book actual N per b K c requested power tag credit bk kn deep vc ck next span panel file stations axes homes names first top κ pt printed y (test s) (capFee s hs)
    simpa only [row,w,θ,mark,same] using entry
  have vn:v≤N:=((vc.trans ck).trans kn)
  have gp:0<θ:=ActualRunKernelPackets.regulator_pos R N per v vn
  have cash:21≤θ⁻¹:=by simpa only [pow_zero,mul_one] using spend N per vn
  have rich:1≤θ⁻¹:=(by norm_num : (1:ℝ)≤21).trans cash
  have combined:=WilsonOriginalObservedRoseSevenScale.original (row Q) (row J₀) (B.W.wheel.rad.le.trans B.active.le)
    rich (pow_nonneg gp.le J₀) A (base E debt) (fun s hs=>(enrolled s hs).1 Q le_rfl)
    (fun s hs=>(enrolled s hs).1 J₀ retained) (fun s hs=>(enrolled s hs).2)
  exact combined.trans (paid_cut gp cash target E debt width)

end YM.Integration.WilsonOriginalObservedRosePublicConnected
end
