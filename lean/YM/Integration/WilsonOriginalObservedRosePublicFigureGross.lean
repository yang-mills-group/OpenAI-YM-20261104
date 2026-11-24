import YM.Integration.WilsonOriginalObservedRoseMovingAbsolute
import YM.Integration.WilsonOriginalObservedRosePublicGross
import YM.Integration.WilsonOriginalObservedRoseMovingBoundary
import YM.Integration.WilsonOriginalObservedRoseMovingKinetic
import YM.Integration.WilsonOlderFreshSoftSocketCensus
import YM.Integration.WilsonOriginalObservedRosePublicVotes
import YM.Integration.WilsonOriginalObservedRoseMovingTail
import YM.Integration.WilsonOriginalObservedRosePublicCurrency

/-! Source-matched enrollment of the physical Rose, its independently normalized high and low figures, and its actual finite kinetic boundary. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRosePublicFigureGross
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


open WilsonOriginalObservedRosePublicGross (base)
open WilsonOlderFreshSoftSocketTotal (figure)
open WilsonOlderFreshSoftSocketRestored (degree)
open WilsonOlderFreshSoftSocketFaces (fill)

private theorem seven (s:Finset (Fin 3))(q:Selection R ages s):
    degree R ages s (fill R ages s q)≤7:=by
  have half:=WilsonOlderFreshSoftSocketCensus.rank R ages s (fill R ages s q)
  have all:WilsonCoeffUV.Wheel.Mark.mass ages s≤WilsonCoeffUV.Wheel.Mark.mass ages Finset.univ:=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun _ _ _=>Nat.zero_le _)
  have total:WilsonCoeffUV.Wheel.Mark.mass ages Finset.univ=14:=by decide
  omega


theorem original (simple:G.Simple)(bliss:Bliss F l z H)(lead:Leading F Jr)
    (obedient:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    (slow:WilsonWindowReportingPace.Slow R.kit)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (cap:∀j,1≤((P).budget j).supportExponent)(upper:∀j,((P).budget j).supportExponent≤100)
    (quote:OPE.Therm.Poetry (P))(color:G.ColorIndex)
    (funded:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε (prepared schedule) R crop W)
    (paths:FundedOriginalVacuumPaths.prices R.kit):
    ∃bank:ℕ,∀debt mesh:ℕ,∃U:Set ℝ,U∈trail ∧
    ∀Q J₀:ℕ,J₀+9≤Q → ∀L:ℕ,∀D:Fin 3→ℕ,∀s:(J).Mode,s.val.Nonempty → ∀X:ℝ,0≤X →
    ∀ᶠv:ℕ in atTop,∀V:Realm G (Q+1) Credit.leanC,∀draw:V.draws=P,V.paid=R.metals.O → V.y=zz P →
    V.anchor≤v → Dormitory V (WilsonCoeffUV.Wheel.Mark.mass ages s.val) 0 Credit.leanC →
    ∀r∈U,∀{T:ℕ}(B:Book F (l:=l) H z 6 T r),WilsonMovingForkWindowBooks.Priced F B →
    ∀actual:Next.UVStress.Lifts (C) B.k,∀(N per b K c requested power tag:ℕ)(credit:ℝ)(bk:b≤K)(kn:K≤N),b<N →
    v≤c → c≤K → v+1≤K → σ K-σ v≤L*Real.log (β v) →
    ∀(panel:Panel R ages N per b K bk kn requested power tag credit)(file:Filed R ages K),
    panel.slot=file.station → panel.axis=file.A N per → (∀i,panel.slot i=B.W.k) →
    (∀i,panel.names i=WilsonNeutralOffsetCutoff.named R (group F Jr Z B actual) N per i) →
    let θ:=g N per v
    (a B.W.k)/(a K)≤(θ⁻¹)^mesh → r/(a K)≤(θ⁻¹)^mesh →
    ∀(κ:(i:Fin 3)→Knob (D i))(pt:Fin 3→Chamber)(cells:Digits V.draws (Fin 3))
      (y:Fin 3→ Cover)(test:Pen D s.val→L[ℝ]ℝ),‖test‖≤X*(θ⁻¹)^debt →
    let w:=votes R ages (N:=N) (per:=per) file panel.names panel.turn
    let path:=cast (congrArg (fun q=>Digits q (Fin 3)) draw) cells
    let row:=normalized R ages κ pt N per K c v path s.val w y test
    let m:=base bank debt+mesh*height ages s.val
    (∀k:ℕ,k≤Q → r^(height ages s.val)*‖row k θ‖≤(θ⁻¹)^m) ∧
      r^(height ages s.val)*‖row Q θ-row J₀ θ‖≤(θ⁻¹)^m*θ^J₀ ∧
      r^(height ages s.val)*‖figure R ages κ pt N per K c v path s.val w y test Q θ-row Q θ‖≤(θ⁻¹)^m*θ^J₀:=by
  obtain ⟨M,E,m0,books⟩:=WilsonOriginalObservedRosePublicVotes.original F Jr Z simple bliss lead obedient slow shop cap upper quote
  refine ⟨E,?_⟩
  intro debt mesh
  have radius:∀ᶠr:ℝ in trail,0<r:=self_mem_nhdsWithin
  obtain ⟨U,active,onU⟩:=((books mesh).and radius).exists_mem
  refine ⟨U,active,?_⟩
  intro Q J₀ retained L D s occupied X xp
  have kept:J₀≤Q:=by omega
  let wage:=wallet R ages M s.val
  have wpos:0≤wage:=Finset.prod_nonneg fun i _=>mul_nonneg
    (Finset.sum_nonneg fun q _=>WilsonReceivedCanonicalVersePortfolio.nonneg R ages i q) (m0 i)
  let bill:=wage*(4:ℝ)^E
  let raw:=2*fixed R D ages Q s.val
  have gpos:0≤raw:=mul_nonneg (by norm_num) (fixed_nonneg R D ages Q s.val)
  have bpos:0≤bill:=mul_nonneg wpos (by positivity)
  filter_upwards [WilsonOriginalObservedRoseMovingBoundary.original R D ages Q s.val occupied simple L,
    WilsonOriginalObservedRoseMovingKinetic.original color funded paths Q J₀ L (by omega),
    WilsonOriginalObservedRoseMovingAbsolute.original R D ages Q s.val occupied simple L,
    WilsonOriginalObservedRoseMovingTail.original R D ages Q J₀ kept s.val occupied simple L,
    WilsonOriginalObservedRosePublicCurrency.clock R simple L E,
    WilsonSeparatedPrefixKineticGeometry.spend R simple (max 1 (bill*X*raw)) 0] with v kinetic settle whole tail clock purse
  intro V draw past price anchor zero r hr T B paid actual N per b K c requested power tag credit bk kn deep vc ck next span panel file stations axes homes names θ age meshRate κ pt cells y test testFee w path row
  have vk:=vc.trans ck
  have gp:0<θ:=ActualRunKernelPackets.regulator_pos R N per v (vk.trans kn)
  have buy:max 1 (bill*X*raw)≤θ⁻¹:=by simpa only [pow_zero,mul_one] using purse N per (vk.trans kn)
  have one:1≤θ⁻¹:=(le_max_left _ _).trans buy
  have rows (i:Fin 3):panel.names i=((B.rows (grade i)).arm true (homogeneous F Jr Z r (grade i) (source C univ i))).source (N,per):=
    (names i).trans ((B.rows (grade i)).weak _ _).symm
  have top:=(onU r hr).1 B paid actual N per b K requested power tag credit bk kn deep panel file stations axes homes rows s θ⁻¹ one age meshRate
  have weights:=clock N per K vk kn span
  have high:=tail V draw past price anchor zero N per K c vc ck kn next span κ pt cells w y test
  have charged:r^(height ages s.val)*(∑q:Selection R ages s.val,‖weight R ages N per K w s.val q‖)≤
      bill*(θ⁻¹)^(2*E)*(θ⁻¹)^(mesh*height ages s.val+1):=by
    calc _≤wage*(β K)^E*(θ⁻¹)^(mesh*height ages s.val+1):=top
         _≤wage*((4:ℝ)^E*(θ⁻¹)^(2*E))*(θ⁻¹)^(mesh*height ages s.val+1):=by gcongr
         _=bill*(θ⁻¹)^(2*E)*(θ⁻¹)^(mesh*height ages s.val+1):=by dsimp only [bill];ring
  intro m
  let z:=θ⁻¹
  let h:=height ages s.val
  let paidMass:=∑q:Selection R ages s.val,‖weight R ages N per K w s.val q‖
  have rp:0≤r^h:=pow_nonneg (onU r hr).2.le _
  have zp:0≤z:=(inv_pos.mpr gp).le
  let e:=2*E+debt+2+mesh*h
  have capital:r^h*paidMass*(‖test‖*raw)≤z^e:=calc
    _≤(bill*z^(2*E)*z^(mesh*h+1))*(X*z^debt*raw):=mul_le_mul charged (mul_le_mul_of_nonneg_right testFee gpos)
      (mul_nonneg (norm_nonneg test) gpos) (mul_nonneg (mul_nonneg bpos (pow_nonneg zp _)) (pow_nonneg zp _))
    _=(bill*X*raw)*z^(2*E+(mesh*h+1)+debt):=by simp only [pow_add];ring
    _≤z*z^(2*E+(mesh*h+1)+debt):=mul_le_mul_of_nonneg_right ((le_max_right _ _).trans buy) (pow_nonneg zp _)
    _=z^e:=by rw [←pow_succ'];congr 1;dsimp only [e];omega
  have nextCoin:e+1=m:=by dsimp only [m,e,h,WilsonOriginalObservedRosePublicGross.base];omega
  constructor
  · intro k kQ
    have entry:=whole V draw past price anchor zero N per K c vc ck kn next span κ pt cells w y test k kQ
    calc r^h*‖row k θ‖≤r^h*(paidMass*(‖test‖*raw*z)):=mul_le_mul_of_nonneg_left entry rp
         _=(r^h*paidMass*(‖test‖*raw))*z:=by ring
         _≤z^e*z:=mul_le_mul_of_nonneg_right capital zp
         _=z^m:=by rw [←pow_succ,nextCoin]
  constructor
  · calc r^h*‖row Q θ-row J₀ θ‖≤r^h*(paidMass*(‖test‖*raw*θ^J₀)):=mul_le_mul_of_nonneg_left high rp
         _=(r^h*paidMass*(‖test‖*raw))*θ^J₀:=by ring
         _≤z^e*θ^J₀:=mul_le_mul_of_nonneg_right capital (pow_nonneg gp.le _)
         _≤z^m*θ^J₀:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one (by omega)) (pow_nonneg gp.le _)

  · have issued:=settle N per K vk kn span
    have due:=kinetic V draw past price anchor zero N per K c vc ck kn next span κ pt cells w y test J₀ 7
      (fun q=>seven (R:=R) s.val q) (by omega) issued
    calc r^h*‖figure R ages κ pt N per K c v path s.val w y test Q θ-row Q θ‖≤
          r^h*(paidMass*(θ^J₀*(‖test‖*raw*z))):=mul_le_mul_of_nonneg_left due rp
         _=(r^h*paidMass*(‖test‖*raw))*z*θ^J₀:=by ring
         _≤z^e*z*θ^J₀:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right capital zp) (pow_nonneg gp.le _)
         _=z^m*θ^J₀:=by rw [←pow_succ,nextCoin]

end YM.Integration.WilsonOriginalObservedRosePublicFigureGross
end
