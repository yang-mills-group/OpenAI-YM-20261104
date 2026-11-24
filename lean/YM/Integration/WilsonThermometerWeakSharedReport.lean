import YM.Integration.WilsonThermometerWeakProjectedFieldMenu
import YM.Integration.WilsonCapturedPrimaryWardRelay

/-! Refile every fixed horizon at its own actual reporting date on the
original route. The finite rank and Ward experiment may have used a separate
earlier mesh for each grade. The filed fields share one regulator and date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakSharedReport
open Function Filter Set Lattice RG Wilson Spec Extraction Cells
open YM.Integration.WilsonLimitConstruction
open PhysicalNext.Repeat.Legato Next.Rank Next.Rank.Tapes.West Next.Rank.East
open PhysicalNext.RankCovariance MergeProof.East Trace.Over
open scoped Topology Classical

open PhysicalNext PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Ship Next.Rank.Station Next.Rank.Spindle
open Function Filter Set Metric Source RG12 Extra.Histories RG05Readout Native Address Many Records Harvest Push.GridApprox Cells Extraction
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Tapes.West Configuration Normal Rise
open Paint Thirst Relation Perch Glimmer LiftMark Beamer Station Atlas Tariffs Ribbon
open Edition Peak Value Marker Corona Alarm Next.Rank.Glyph
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonAddressedWeakCalibration WilsonAddressedWeakReflectedHearing WilsonThermometerReflectedTrajectory
open FVA2 FVA2.ColorCode Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone PhysMS
open Trace Trace.Pilot WilsonAddressedWeakCorrectedCylinder WilsonAddressedWeakPointCells WilsonAddressedWeakMaxwellPositions
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} (R:Run G) {d H:ℕ}
local notation "Rf" => R.family
local notation "Lev" => R.family.path.levels
local notation "cash" => WilsonThermometerOffsetLedger.cash R

variable {C:Local.Physical.Deck G} {O₀:Booked C} (M:MS_Data G O₀)

open WilsonThermometerWeakPanelBorn WilsonThermometerSmallPanelRead
open WilsonThermometerWeakJointWidth WilsonPositionThermometerStationNorm
open WilsonAddressedWeakFixedChild WilsonAddressedWeakCalibration

open WilsonThermometerWeakWardRows (inverseBill)
open WilsonThermometerOwnOffsetField Push Trace.Pilot Next.Extract MergeProof
variable (V:∀d,Source.SectionData (R.family.labels.level d)) (W:Mark.Weave G)
    {P:∀d,(ℕ×ℕ)→(R.family.label d≃ₗ[ℂ]R.family.label d)} (b:Presentation R.family)
    (portfolio:∀d,Mark.Portfolio R.family.params (V d) (W d))
    (house:Hearthside R.family V W P b (PhysicalNext.Repeat.Legato.Bandage.fly R.alloy.B.a))

open WilsonCapturedPrimaryWardRetimed (reading)

def gradeFiled (b:Presentation R.family) (d:ℕ) (f:Extraction.Order)
    (hier:(Cells.standard Rf).Hierarchy) (ε E:ℝ) {ℓ N:ℕ} (late:ℓ<N) :Prop:=
    ∀(p:ℕ)(z:Site ((Rf).side N p))(V₀:Sight Rf d p)(r:Emblems Rf d),
    Enrolled R.makes R.doors cash ℓ N p d (digits R N p z) V₀ r →
    ∀{D:ℕ}(T:Vane Rf D)(shelf:d≤D),let j:Fin (D+1):=⟨d,by omega⟩
    ∀v:(Cells.standard Rf).Field j, T.k=ℓ → T.checked f hier D →
    ∃y:Palette Rf d,b.step d (N,p) (reading (p:=p) r late.le y)=b.step d (N,p) (T.wheel.atCut (N,p) j v) ∧
      size y≤E*((Lev).clock.hatBeta ℓ)^ε*(cost Rf d*‖v‖)

include M V W b portfolio house
theorem priced (d:ℕ) (simple:G.Simple) (paid:R2I.RG05Joint.AcrossPanels R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G) (W₀:Warehouse G)
    (μ ε:ℝ) (pos:0<ε) (f:Extraction.Order) (hier:(Cells.standard Rf).Hierarchy) :
    ∃E:ℝ,0≤E ∧ ∀ᶠ ℓ:ℕ in atTop,∀ᶠ N:ℕ in atTop,∃late:ℓ<N,gradeFiled R b d f hier ε E late:=by
  let η:=ε/((d:ℝ)+2)
  let τ:=min 1 η
  have good:0<η:=by dsimp only [η];positivity
  have tp:0<τ:=lt_min zero_lt_one good
  obtain ⟨E,hE,early⟩:=WilsonThermometerWeakProjectedFieldMenu.withSpan R M V W b portfolio house d
    simple paid shop S W₀ μ η good f hier
  have available:=WilsonThermometerOffsetLedger.original R simple shop d
  obtain ⟨floor,free⟩:=eventually_atTop.mp (available.and (WilsonCapturedPrimaryWardRetimed.cash (Rf)))
  refine ⟨E,hE,?_⟩
  filter_upwards [early floor τ tp (min_le_left ..)] with ℓ issued
  obtain ⟨k,begin,prior,ratio,dated⟩:=issued
  let β:ℝ:=(Lev).clock.hatBeta ℓ
  let L:=β^η
  have β₁:1≤β:=((Lev).fits.delayed ℓ).le
  have large:1≤L:=Real.one_le_rpow β₁ good.le
  have forward:(Rf).S.a k/(Rf).S.a ℓ≤L:=ratio.trans (Real.rpow_le_rpow_of_exponent_le β₁ (min_le_right ..))
  have reverse:(Rf).S.a ℓ/(Rf).S.a k≤L:=((div_le_one ((Rf).S.a_pos k)).2 ((Rf).S.strictAnti.antitone prior)).trans large
  filter_upwards [dated] with N late
  obtain ⟨strict,offer⟩:=late
  refine ⟨strict,?_⟩
  intro p z V₀ r fellow D T shelf j v stationed checked
  obtain ⟨V₁,r₁,learnt,send,kept⟩:=WilsonCapturedPrimaryWardRelay.original fellow (prior.trans strict.le) strict.le
    (free k begin).1.1 large forward reverse (free k begin).2 (free ℓ (begin.trans prior)).2
  obtain ⟨y,projected,priced⟩:=offer p z V₁ r₁ learnt T shelf v stationed checked
  have own: b.step d (N,p) (reading (p:=p) r₁ (prior.trans strict.le) y)=_:=projected
  refine ⟨send y,(congrArg (b.step d (N,p)) (kept y).1).trans own,(kept y).2.trans ?_⟩
  have power: L^(d+1)*L=β^ε:=by
    rw [←pow_succ,←Real.rpow_natCast,←Real.rpow_mul (zero_lt_one.trans_le β₁).le]
    congr 1
    dsimp only [η]
    push_cast
    field_simp
    ring
  calc
    _ ≤ L^(d+1)*(E*L*(cost Rf d*‖v‖)):=mul_le_mul_of_nonneg_left priced (pow_nonneg (zero_le_one.trans large) _)
    _ = E*(L^(d+1)*L)*(cost Rf d*‖v‖):=by ring
    _ = _ :=by rw [power]

theorem original (H:ℕ) (simple:G.Simple) (paid:R2I.RG05Joint.AcrossPanels R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G) (W₀:Warehouse G)
    (μ ε:ℝ) (pos:0<ε) (f:Extraction.Order) (hier:(Cells.standard Rf).Hierarchy) :
    ∃E:Fin (H+1)→ℝ,(∀d,0≤E d) ∧ ∀ᶠ ℓ:ℕ in atTop,∀ᶠ N:ℕ in atTop,∃late:ℓ<N,
      ∀d:Fin (H+1),gradeFiled R b d f hier ε (E d) late:=by
  choose E positive dates using fun d:Fin (H+1)=>priced R M V W b portfolio house d simple paid shop S W₀ μ ε pos f hier
  refine ⟨E,positive,?_⟩
  filter_upwards [eventually_all.mpr dates] with ℓ stage
  filter_upwards [eventually_all.mpr stage,eventually_gt_atTop ℓ] with N manifests late
  exact ⟨late,fun d=>(manifests d).choose_spec⟩

end YM.Integration.WilsonThermometerWeakSharedReport
end
