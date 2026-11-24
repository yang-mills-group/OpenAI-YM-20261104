import YM.Integration.WilsonThermometerWeakSharedReport

/-! On a true displaced site the funded representatives may be chosen as one
linear map of the original reported test. This preserves all linear combinations
before integrating any supported test or multiplying independent source arms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakLinearReport
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

open WilsonThermometerWeakSharedReport (gradeFiled)
abbrev coords (C:Family G) (d:ℕ):=Module.finBasis ℂ ((Cells.standard C).Field d)
def factor (C:Family G) (d:ℕ):ℝ:=∑a,‖((coords C d).coord a).toContinuousLinearMap‖*‖coords C d a‖

def linearFiled (b:Presentation Rf) (d:ℕ) (f:Extraction.Order) (hier:(Cells.standard Rf).Hierarchy)
    (ε A:ℝ) {ℓ N:ℕ} (late:ℓ<N) :Prop:=
  ∀(p:ℕ)(z:Site ((Rf).side N p))(V₀:Sight Rf d p)(r:Emblems Rf d),
  Enrolled R.makes R.doors cash ℓ N p d (digits R N p z) V₀ r →
  ∀{D:ℕ}(T:Vane Rf D)(shelf:d≤D),let j:Fin (D+1):=⟨d,by omega⟩
  T.k=ℓ → T.checked f hier D → ∃L:(Cells.standard Rf).Field j →ₗ[ℂ] Palette Rf d,
    ∀v, b.step d (N,p) (reading (p:=p) r late.le (L v))=b.step d (N,p) (T.wheel.atCut (N,p) j v) ∧
      size (L v)≤A*((Lev).clock.hatBeta ℓ)^ε*(cost Rf d*‖v‖)

theorem choose (d:ℕ) (f:Extraction.Order) (hier:(Cells.standard Rf).Hierarchy)
    (ε A:ℝ) (nonneg:0≤A) {ℓ N:ℕ} (late:ℓ<N) (given:gradeFiled R b d f hier ε A late) :
    linearFiled R b d f hier ε (factor (Rf) d*A) late:=by
  classical
  intro per z data r enrolled D T shelf j station checked
  let B:=coords (Rf) d
  let g:=((Lev).clock.hatBeta ℓ)^ε
  let B₀:=A*g*cost Rf d
  have hβ:0≤((Lev).clock.hatBeta ℓ):=zero_le_one.trans ((Lev).fits.delayed ℓ).le
  have hb:0≤B₀:=by dsimp only [B₀,g,cost];positivity
  choose Y exact_at paid using fun i=>given per z data r enrolled T shelf (B i) station checked
  let L:(Cells.standard Rf).Field d →ₗ[ℂ] Palette Rf d:=∑i,(B.coord i).smulRight (Y i)
  have eval (v):L v=∑i,(B.coord i v) • Y i:=by simp only [L,LinearMap.sum_apply,LinearMap.smulRight_apply]
  let π:=(b.step d (N,per))
  let U:=WilsonThermometerWeakFourLinearRows.entrance R (p:=per) r late.le
  let X:=T.wheel.atCut (N,per) j
  refine ⟨L,fun v=>⟨?_,?_⟩⟩
  · change π (U (L v))=π (X v)
    calc
      _ = ∑i,(B.coord i v) • π (U (Y i)):=by simp only [eval,map_sum,map_smul]
      _ = ∑i,(B.coord i v) • π (X (B i)):=Finset.sum_congr rfl fun i _=>congrArg ((B.coord i v) • ·) (exact_at i)
      _ = π (X (∑i,(B.coord i v) • B i)):=by simp only [map_sum,map_smul]
      _ = π (X v):=congrArg (fun w=>π (X w)) (B.sum_repr v)
  · rw [eval]
    refine (size_sum _ _).trans ?_
    calc
      _ ≤ ∑i,(‖(B.coord i).toContinuousLinearMap‖*‖B i‖)*(B₀*‖v‖):=Finset.sum_le_sum fun i _=>by
        rw [size_smul]
        have bound:‖B.coord i v‖≤‖(B.coord i).toContinuousLinearMap‖*‖v‖:=(B.coord i).toContinuousLinearMap.le_opNorm _
        have pay:size (Y i)≤B₀*‖B i‖:=by simpa only [B₀,g,mul_assoc] using paid i
        calc
          _ ≤ (‖(B.coord i).toContinuousLinearMap‖*‖v‖)*(B₀*‖B i‖):=mul_le_mul bound pay (size_ge _) (le_trans (norm_nonneg (B.coord i v)) bound)
          _ = _ :=by ring
      _ = (factor (Rf) d*A)*g*(cost Rf d*‖v‖):=by rw [←Finset.sum_mul];dsimp only [factor,B,B₀];ring

include M V W b portfolio house
theorem original (H:ℕ) (simple:G.Simple) (paid:R2I.RG05Joint.AcrossPanels R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G) (W₀:Warehouse G)
    (μ ε:ℝ) (pos:0<ε) (f:Extraction.Order) (hier:(Cells.standard Rf).Hierarchy) :
    ∃E:Fin (H+1)→ℝ,(∀d,0≤E d) ∧ ∀ᶠ ℓ:ℕ in atTop,∀ᶠ N:ℕ in atTop,∃late:ℓ<N,
      ∀d:Fin (H+1),linearFiled R b d f hier ε (E d) late:=by
  obtain ⟨A,hA,prices⟩:=WilsonThermometerWeakSharedReport.original R M V W b portfolio house H simple paid shop S W₀ μ ε pos f hier
  refine ⟨fun d=>factor (Rf) d*A d,fun d=>mul_nonneg (by unfold factor;positivity) (hA d),?_⟩
  filter_upwards [prices] with ℓ seated
  filter_upwards [seated] with N receipt
  obtain ⟨late,offered⟩:=receipt
  exact ⟨late,fun d=>WilsonThermometerWeakLinearReport.choose R b d f hier ε (A d) (hA d) late (offered d)⟩

end YM.Integration.WilsonThermometerWeakLinearReport
end
