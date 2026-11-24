import YM.Integration.WilsonThermometerWeakFourLinearRows
import YM.Integration.WilsonThermometerWeakPanelSubpower
/-! The two displaced grade-four legs are issued on their own Wilson programmes.
The enrolled near site and all operator fees precede the inner cutoff and period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakFourMeasuredMenu
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

open WilsonThermometerWeakFourLinearRows WilsonThermometerOwnOffsetField Push Trace.Pilot Next.Extract MergeProof
variable (V:∀d,Source.SectionData (R.family.labels.level d)) (W:Mark.Weave G)
    {P:∀d,(ℕ×ℕ)→(R.family.label d≃ₗ[ℂ]R.family.label d)} (b:Presentation R.family)
    (house:Hearthside R.family V W P b (PhysicalNext.Repeat.Legato.Bandage.fly R.alloy.B.a))

private theorem rise (simple:G.Simple):Monotone ((Lev).clock.hatBeta):=by
  intro i j h
  unfold Calendar.hatBeta
  rw [add_le_add_iff_left]
  exact mul_le_mul_of_nonneg_left ((Ribbons.bob (Rf).S).monotone h) (Gauge.slopeConstant_pos simple).le

include M V W b house
theorem withSpan (simple:G.Simple) (paid:R2I.RG05Joint.AcrossPanels R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G) (W₀:Warehouse G)
    (μ ε:ℝ) (pos:0<ε) (f:Extraction.Order) (hier:(Cells.standard Rf).Hierarchy) :
    ∃E:ℝ, 0≤E ∧ ∀(floor:ℕ)(τ:ℝ),0<τ → τ≤1 →∀ᶠ ℓ:ℕ in atTop,∃k:ℕ, floor≤k ∧ ∃later:k≤ℓ, (Rf).S.a k/(Rf).S.a ℓ≤(Lev).clock.hatBeta ℓ^τ ∧
      ∀ᶠ N:ℕ in atTop,∃late:ℓ<N,∀p,
      let hk:=later.trans late.le
      ∀ (z:Site ((Rf).side N p)) (V₀:Sight Rf 4 p) (r:Emblems Rf 4),
      Enrolled R.makes R.doors cash k N p 4 (digits R N p z) V₀ r →
      ∀{D':ℕ}(T:Vane Rf D') (shelf:4≤D'), let j:Fin (D'+1):=⟨4,by omega⟩
      ∀v:(Cells.standard Rf).Field j, T.k=ℓ → T.checked f hier D' →
      ∃y:Palette Rf 4,
      (((Rf).S.a k:ℂ)^4) • ((Rf).factory 4 N p).terminal (finer r hk y (primaryLetter 4))
          =T.wheel.atCut (N,p) j v ∧ size y≤E*((Lev).clock.hatBeta ℓ)^ε*(cost Rf 4*‖v‖):=by
  let η:=ε/3
  have positive:0<η:=by dsimp [η];positivity
  obtain ⟨w,Q,B,cap,exam,_,Qge,Bpos,dated⟩:=
   WilsonThermometerWeakFourMixedRoster.withSpan R M simple paid shop S W₀ μ η positive f hier
  obtain ⟨k₀,cheap⟩:=eventually_atTop.mp (WilsonThermometerWeakPanelSubpower.original (Lev) simple exam positive)
  let K:=MSDeckProbeGram.matrix M 4 0 w μ 0
  let n:ℝ:=Fintype.card (Glyph C 4)
  let S₄:=2*scaleCost Rf 4
  let E:=n*inverseBill K*(Q*B*S₄)*n
  have hn:0≤n:=by dsimp only [n];positivity
  have hI:0 ≤ inverseBill K:=by unfold inverseBill;positivity
  have hS:0≤S₄:=by unfold S₄ scaleCost;positivity
  have hE:0≤E:=by dsimp only [E];positivity
  refine ⟨E,hE,?_⟩
  intro floor τ τpos τone
  filter_upwards [dated (max floor k₀) τ τpos τone] with ℓ choice
  obtain ⟨k,start,later,span,dates⟩:=choice
  refine ⟨k,(le_max_left ..).trans start,later,span,?_⟩
  filter_upwards [dates] with N run
  obtain ⟨late,program⟩:=run
  refine ⟨late,?_⟩
  intro p hk z V₀ r financed
  let loc:=WilsonThermometerWeakFourMixedRoster.locations R hk w exam.arc (fun _=>z)
  obtain ⟨u,rent,invert,close,mixed⟩:=program p (fun _=>z) (fun _=>V₀) (fun _=>r) (fun _=>financed)
  let β:ℝ:=(Lev).clock.hatBeta ℓ
  have βpos:0<β:=zero_lt_one.trans ((Lev).fits.delayed ℓ)
  let g:=β^η
  have gpos:0<g:=Real.rpow_pos_of_pos βpos _
  have each (i:Fin 2) (a:Glyph C 4):((Rf).labels.level 4).coeffSize (u i a)≤g:=by
    have loan:=rent i a
    rw [size_chunk] at loan
    exact (loan.trans (cheap k (by omega))).trans (Real.rpow_le_rpow (zero_lt_one.trans ((Lev).fits.delayed k)).le (rise R simple later) positive.le)
  intro D' T shelf j v station rules
  let x:=(T.wheel.atCut (N,p) j v)
  let cost₀:=cost Rf 4*‖v‖
  have hcost:0≤cost₀:=by unfold cost₀ cost;positivity
  let q:ℝ:=(Q*g*cost₀)*(B*(S₄*g))
  have hq:0≤q:=by dsimp only [q];positivity
  have wage (a:Glyph C 4):
      ‖moment ((Rf).beta N p) (fun U=>(Rf).O N p x (loc 0) U*arm R r hk (loc 1) (u 1 a) U)‖≤q:=by
    exact (mixed T j v rfl station rules a).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (each 1 a) hS) Bpos.le) (by positivity))
  obtain ⟨y,literal,price⟩:=WilsonThermometerWeakFourLinearRows.earned R V W b house simple loc (fun _=>r) hk u K invert close x q hq wage
  refine ⟨y,literal,price.trans ?_⟩
  have sum:(∑i,((Rf).labels.level 4).coeffSize (u 0 i))≤n*g:=by
    calc
      _ ≤ ∑_i:Glyph C 4,g:=Finset.sum_le_sum (fun i _=>each 0 i)
      _ = _ := by simp [n]
  have cube:g^3=β^ε:=by
    change (β^η)^3=β^ε
    rw [←Real.rpow_natCast (β^η) 3,←Real.rpow_mul βpos.le]
    congr 1
    dsimp [η]
    ring
  calc
    _ ≤ (n*inverseBill K*q)*(n*g):=mul_le_mul_of_nonneg_left sum (by positivity)
    _ = E*g^3*cost₀:=by dsimp only [E,q];ring
    _ = _ :=by rw [cube]

theorem original (simple:G.Simple) (paid:R2I.RG05Joint.AcrossPanels R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G) (W₀:Warehouse G)
    (μ ε:ℝ) (pos:0<ε) (f:Extraction.Order) (hier:(Cells.standard Rf).Hierarchy) :
    ∃E:ℝ, 0≤E ∧ ∀floor:ℕ,∀ᶠ ℓ:ℕ in atTop,∃k:ℕ, floor≤k ∧ ∃later:k≤ℓ,
      ∀ᶠ N:ℕ in atTop,∃late:ℓ<N,∀p,
      let hk:=later.trans late.le
      ∀ (z:Site ((Rf).side N p)) (V₀:Sight Rf 4 p) (r:Emblems Rf 4),
      Enrolled R.makes R.doors cash k N p 4 (digits R N p z) V₀ r →
      ∀{D':ℕ}(T:Vane Rf D') (shelf:4≤D'), let j:Fin (D'+1):=⟨4,by omega⟩
      ∀v:(Cells.standard Rf).Field j, T.k=ℓ → T.checked f hier D' →
      ∃y:Palette Rf 4,
      (((Rf).S.a k:ℂ)^4) • ((Rf).factory 4 N p).terminal (finer r hk y (primaryLetter 4))
          =T.wheel.atCut (N,p) j v ∧ size y≤E*((Lev).clock.hatBeta ℓ)^ε*(cost Rf 4*‖v‖) :=by
  obtain ⟨E,hE,paidAt⟩:=withSpan R M V W b house simple paid shop S W₀ μ ε pos f hier
  refine ⟨E,hE,?_⟩
  intro floor
  filter_upwards [paidAt floor 1 zero_lt_one le_rfl] with ℓ event
  obtain ⟨k,start,later,_,taken⟩:=event
  exact ⟨k,start,later,taken⟩

end YM.Integration.WilsonThermometerWeakFourMeasuredMenu
end
