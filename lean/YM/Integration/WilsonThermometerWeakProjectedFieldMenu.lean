import YM.Integration.WilsonThermometerWeakJointWardSolve
import YM.Integration.WilsonThermometerWeakPanelSubpower
import YM.Integration.WilsonThermometerReferenceStation

/-! The actual original weak date and its filed group vector have a true
equation-ideal projected representation with a before-period subpower tariff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakProjectedFieldMenu
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

private theorem rise (simple:G.Simple):Monotone ((Lev).clock.hatBeta):=by
  intro i j h
  unfold Calendar.hatBeta
  rw [add_le_add_iff_left]
  exact mul_le_mul_of_nonneg_left ((Ribbons.bob (Rf).S).monotone h) (Gauge.slopeConstant_pos simple).le

private theorem upperFade (A:ℝ):∀ᶠ N:ℕ in atTop,Real.exp (-(3/128:ℝ)*(Rf).S.scale N)*A≤1:=by
  have gone:Tendsto (fun N:ℕ=>Real.exp (-(3/128:ℝ)*(Rf).S.scale N)) atTop (𝓝 0):=
    Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (by norm_num) (Rf).S.divergent)
  have small:Tendsto (fun N:ℕ=>Real.exp (-(3/128:ℝ)*(Rf).S.scale N)*A) atTop (𝓝 0):=by
    simpa only [zero_mul] using gone.mul_const A
  exact small.eventually_le_const (by norm_num)

private theorem stationPrice (simple:G.Simple) (d:ℕ) (η:ℝ) (pos:0<η)
    (f:Extraction.Order) (hier:(Cells.standard Rf).Hierarchy):
    ∀ᶠ ℓ in atTop,∀{D:ℕ}(T:Vane Rf D)(j:Fin (D+1)),j.val=d → T.k=ℓ → T.checked f hier D →
    ∀(v:(Cells.standard Rf).Field j)(N p:ℕ),ℓ<N →
      ((Rf).labels.level j).coeffSize (T.wheel.atCut (N,p) j v)≤
        Real.exp (Work.D01.columnLogs (Lev) ℓ)*(((Lev).clock.hatBeta ℓ)^η*(cost Rf d*‖v‖)):=by
  exact WilsonThermometerReferenceStation.cutoff (C:=R.family) (f:=f) (H:=hier) simple R.makes d η pos

include M V W b portfolio house
theorem withSpan (d:ℕ) (simple:G.Simple) (paid:R2I.RG05Joint.AcrossPanels R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G) (W₀:Warehouse G)
    (μ ε:ℝ) (pos:0<ε) (f:Extraction.Order) (hier:(Cells.standard Rf).Hierarchy) :
    ∃E:ℝ, 0≤E ∧ ∀(floor:ℕ)(τ:ℝ),0<τ → τ≤1 →∀ᶠ ℓ:ℕ in atTop,∃k:ℕ, floor≤k ∧ ∃later:k≤ℓ, (Rf).S.a k/(Rf).S.a ℓ≤(Lev).clock.hatBeta ℓ^τ ∧
      ∀ᶠ N:ℕ in atTop,∃late:ℓ<N,∀p,
      let hk:=later.trans late.le
      ∀ (z:Site ((Rf).side N p)) (V₀:Sight Rf d p) (r:Emblems Rf d),
      Enrolled R.makes R.doors cash k N p d (digits R N p z) V₀ r →
      ∀{D':ℕ}(T:Vane Rf D') (shelf:d≤D'), let j:Fin (D'+1):=⟨d,by omega⟩
      ∀v:(Cells.standard Rf).Field j, T.k=ℓ → T.checked f hier D' →
      ∃y:Palette Rf d,
      b.step d (N,p) ((((Rf).S.a k:ℂ)^d) • ((Rf).factory d N p).terminal (finer r hk y (primaryLetter d)))
          =b.step d (N,p) (T.wheel.atCut (N,p) j v) ∧ size y≤E*((Lev).clock.hatBeta ℓ)^ε*(cost Rf d*‖v‖):=by
  let η:=ε/3
  have positive:0<η:=by dsimp [η];positivity
  obtain ⟨radius,solver⟩:=WilsonThermometerWeakJointWardSolve.original R V W P b portfolio house simple C d
  obtain ⟨j₀,openN⟩:=eventually_atTop.mp solver
  obtain ⟨w,Q,B,cap,exam,_,Qge,Bpos,dated⟩:=
   WilsonThermometerWeakJointWardMenu.original R M d radius simple paid shop S W₀ μ η positive f hier
  obtain ⟨k₀,cheap⟩:=eventually_atTop.mp (WilsonThermometerWeakPanelSubpower.original (Lev) simple exam positive)
  let K:=MSDeckProbeGram.matrix M d 0 w μ 0
  let n:ℝ:=Fintype.card (Glyph C d)
  let S₄:=2*scaleCost Rf d
  let E:=2*(n*inverseBill K)*(Q*B*S₄+1)*n
  have hn:0≤n:=by dsimp only [n];positivity
  have hI:0 ≤ inverseBill K:=by unfold inverseBill;positivity
  have hS:0≤S₄:=by unfold S₄ scaleCost;positivity
  have hE:0≤E:=by dsimp only [E];positivity
  refine ⟨E,hE,?_⟩
  intro floor τ τpos τone
  filter_upwards [dated (max floor (max k₀ j₀)) τ τpos τone,
      stationPrice R simple d η positive f hier] with ℓ choice money
  obtain ⟨k,start,later,span,dates⟩:=choice
  refine ⟨k,(le_max_left ..).trans start,later,span,?_⟩
  let β:ℝ:=(Lev).clock.hatBeta ℓ
  let g:=β^η
  have βpos:0<β:=zero_lt_one.trans ((Lev).fits.delayed ℓ)
  have gpos:0<g:=Real.rpow_pos_of_pos βpos _
  have gOne:1≤g:=Real.one_le_rpow ((Lev).fits.delayed ℓ).le positive.le
  let J:=B*S₄
  let raw:=Real.exp (Work.D01.columnLogs (Lev) ℓ)*g
  let ind:ℝ:=Fintype.card ((Rf).labels.level d).Index
  let shift:ℝ:=‖(((Rf).S.a k:ℂ)^d)‖
  have hJ:0≤J:=mul_nonneg Bpos.le hS
  filter_upwards [dates,openN k (by omega),
    upperFade R (2*(n*inverseBill K)*(2*(J*g)*(shift*(n*g)))),
    upperFade R (2*(J*g)*(ind*raw))] with N run use capX chargeX
  obtain ⟨late,program⟩:=run
  refine ⟨late,?_⟩
  intro p hk z V₀ r financed
  let loc:=WilsonThermometerWeakFourMixedRoster.locations R hk w exam.arc (fun _=>z)
  obtain ⟨u,rent,invert,close,housing,mixed⟩:=program p (fun _=>z) (fun _=>V₀) (fun _=>r) (fun _=>financed)
  have each (i:Fin 2) (a:Glyph C d):((Rf).labels.level d).coeffSize (u i a)≤g:=by
    have loan:=rent i a
    rw [size_chunk] at loan
    exact (loan.trans (cheap k (by omega))).trans (Real.rpow_le_rpow (zero_lt_one.trans ((Lev).fits.delayed k)).le (rise R simple later) positive.le)
  intro D' T shelf j v station rules
  let x:=(T.wheel.atCut (N,p) j v)
  let cost₀:=cost Rf d*‖v‖
  have hcost:0≤cost₀:=by unfold cost₀ cost;positivity
  let q:ℝ:=(Q*g*cost₀)*(B*(S₄*g))
  have hq:0≤q:=by dsimp only [q];positivity
  have wage (a:Glyph C d):
      ‖moment ((Rf).beta N p) (fun U=>(Rf).O N p x (loc 0) U*arm R r hk (loc 1) (u 1 a) U)‖≤q:=by
    exact (mixed T j v rfl station rules a).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (each 1 a) hS) Bpos.le) (by positivity))
  obtain ⟨_,solve⟩:=use
  let decay:=Real.exp (-(3/128:ℝ)*(Rf).S.scale N)
  let τN:=2*decay*(J*g)
  have τgood:0≤τN:=by dsimp only [τN,decay];positivity
  have affordable:2*(n*inverseBill K)*(τN*(shift*(n*g)))≤1:=by
    calc _ = decay*(2*(n*inverseBill K)*(2*(J*g)*(shift*(n*g)))):=by dsimp only [τN];ring
         _ ≤ _ :=capX
  have χcap:τN*(ind*raw)≤1:=by
    calc _ = decay*(2*(J*g)*(ind*raw)):=by dsimp only [τN];ring
         _ ≤ _ :=chargeX
  have xCost:‖x‖≤raw*cost₀:=by
    refine (YM.Push.Local.norm_le_size ((Rf).labels.level d) _).trans ?_
    simpa only [raw,β,g,cost₀,mul_assoc] using money T j rfl station rules v N p late
  have corr:τN*(ind*‖x‖)≤cost₀:=by
    calc
      _ ≤ τN*(ind*(raw*cost₀)):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left xCost (Nat.cast_nonneg _)) τgood
      _ = (τN*(ind*raw))*cost₀:=by ring
      _ ≤ 1*cost₀:=mul_le_mul_of_nonneg_right χcap hcost
      _ = _ :=one_mul _
  have wK:=WilsonThermometerWeakWardRows.fee (WilsonThermometerWeakWardRows.gram R loc (fun _=>r) hk u) K close
  obtain ⟨y,literal,price⟩:=solve p loc (fun _=>r) u J g (inverseBill K) hJ gpos.le hI housing each
    (digits R N p z) cash V₀ financed invert wK x q hq wage affordable
  refine ⟨y,literal,price.trans ?_⟩
  have corr':τN*(ind*‖x‖)≤g^2*cost₀:=
    corr.trans ((le_mul_of_one_le_left hcost) (one_le_pow₀ gOne))
  have cube:g^3=β^ε:=by
    change (β^η)^3=β^ε
    rw [←Real.rpow_natCast (β^η) 3,←Real.rpow_mul βpos.le]
    congr 1
    dsimp [η]
    ring
  change (2*(n*inverseBill K)*(q+τN*(ind*‖x‖)))*(n*g)≤_
  calc
    _ ≤ (2*(n*inverseBill K)*(q+g^2*cost₀))*(n*g):=by gcongr
    _ = E*g^3*cost₀:=by dsimp only [E,q];ring
    _ = _ :=by rw [cube]

end YM.Integration.WilsonThermometerWeakProjectedFieldMenu
end
