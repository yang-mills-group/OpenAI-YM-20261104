import YM.Integration.WilsonAddressedWeakCommonWindow
import YM.Integration.WilsonThermometerWeakRankCovers
import YM.Integration.WilsonThermometerWeakDisplacedHorizon
import YM.Integration.WilsonThermometerWeakSameRunCross

/-! The two calibrated weak publications and the literal Vane mixed reading
share one cutoff, one bank and the two nominated displaced residues. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakFourMixedRoster
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

def locations {k N p:ℕ} (hk:k≤N) (w:E4) (a:ℝ) (z:Fin 2→Site ((Rf).side N p)):Fin 2→Site ((Rf).side N p):=
  fun i=>slide R hk (z i) (((Rf).S.toDepth hk p).parent
    (WilsonPositionPhysicalCellTest.site (R:=R) (gap (Lev) a k) (N,p) (Extra.FD.couple 0 w) i))

private theorem span {k ℓ:ℕ} (rent:(Rf).S.a k/(Rf).S.a ℓ≤((Lev).clock.hatBeta ℓ)^((1:ℝ))):
    (Rf).S.scale ℓ-(Rf).S.scale k≤Real.log ((Lev).clock.hatBeta ℓ):=by
  rw [Real.rpow_one] at rent
  refine le_trans ?_ (Real.log_le_log (div_pos ((Rf).S.a_pos k) ((Rf).S.a_pos ℓ)) rent)
  unfold Schedule.scale
  rw [Real.log_inv,Real.log_inv,Real.log_div ((Rf).S.a_pos k).ne' ((Rf).S.a_pos ℓ).ne']
  linarith

private theorem wheels (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b):
    ∀ᶠ k in atTop,wheel (Lev) k≤(Lev).clock.monitor k:=by
  filter_upwards [eventually_ge_atTop 1,WilsonThermometerWeakPastBlocks.paid R simple shop] with k one paid
  obtain ⟨t,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega:k≠0)
  change (↑((Lev).clock.factor ((Lev).clock.J (t+1))).val:ℝ) ≤ (Lev).clock.monitor (t+1)
  rw [(Lev).fits.sameFactor t]
  exact paid t (Nat.le_succ _)

theorem withSpan (simple:G.Simple) (paid:R2I.RG05Joint.AcrossPanels R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G) (W:Warehouse G)
    (μ ε:ℝ) (pos:0<ε) (f:Extraction.Order) (hier:(Cells.standard Rf).Hierarchy) :
    ∃(w:E4)(Q B:ℝ)(cap:ℕ)(exam:Panel cap), (0:E4)≠w ∧ 0≤Q ∧ 0<B ∧
    ∀(floor:ℕ)(τ:ℝ),0<τ → τ≤1 → ∀ᶠ ℓ:ℕ in atTop,∃k:ℕ, floor≤k ∧ ∃prior:k≤ℓ, (Rf).S.a k/(Rf).S.a ℓ≤(Lev).clock.hatBeta ℓ^τ ∧ ∀ᶠ N:ℕ in atTop,∃late:ℓ<N,∀p,
      let hk:k≤N:=prior.trans late.le
      let ξ:=exam.bag ((Lev).clock.J k)
      let K:=MSDeckProbeGram.matrix M 4 0 w μ 0
      ∀ (z:Fin 2→Site ((Rf).side N p)) (V₀:Fin 2→Sight Rf 4 p) (r:Fin 2→Emblems Rf 4),
      (∀i,Enrolled R.makes R.doors cash k N p 4 (digits R N p (z i)) (V₀ i) (r i)) →
      let loc:=locations R hk w exam.arc z
      ∃u:Fin 2→Glyph C 4→(Rf).label 4,
      let y:=fun (i:Fin 2)(j:Glyph C 4)=>chunk (C:=Rf) (WilsonThermometerOwnOffsetField.primaryLetter 4) (u i j)
      let A:Matrix (Glyph C 4) (Glyph C 4) ℂ:=fun a e=>reading R (fun _=>4) loc (fun i=>y i (![a,e] i)) r hk full
      (∀i j,size (y i j)≤Perch.bill (ξ.credit-1) (clim (Lev) k)) ∧
      IsUnit A ∧ (∀i j,‖A⁻¹ i j-K⁻¹ i j‖<1) ∧
      ∀{D':ℕ}(V:Vane Rf D') (j:Fin (D'+1)) (v:(Cells.standard Rf).Field j),
      j.val=4 → V.k=ℓ → V.checked f hier D' → ∀a,
      ‖moment ((Rf).beta N p) (fun U=>(Rf).O N p (V.wheel.atCut (N,p) j v) (loc 0) U*arm R (r 1) hk (loc 1) (u 1 a) U)‖≤
      (Q*((Lev).clock.hatBeta ℓ)^ε*(cost (Rf) 4*‖v‖)) *
        (B*((2*scaleCost (Rf) 4)*((Rf).labels.level 4).coeffSize (u 1 a))):=by
  let grade:Fin 5:=⟨4,by norm_num⟩
  obtain ⟨P,κ,e,skyChecks,policy⟩:=WilsonThermometerWeakSameRunCross.original (d:=4) R simple shop
    paid f hier grade ε pos
  obtain ⟨Q,Qpos,mixed⟩:=policy 0
  have arc:0<(P 0).arc:=by linarith only [(P 0).huge]
  obtain ⟨cap,depth,fits⟩:=WilsonThermometerWeakDisplacedHorizon.original (P 0).arc arc e 4
  obtain ⟨K,O,P₀,c,w,B,_,checks,apart,_,posB,dates⟩:=
    WilsonAddressedWeakCommonWindow.original R M paid simple shop S W depth μ 1 zero_lt_one
  let x:=Extra.FD.couple (0:E4) w
  have diff:∃j:Axis,x 0 j≠x 1 j:=by
    by_contra! eq
    apply apart
    ext j
    exact eq j
  have ea:0<(P₀ 2).arc:=by linarith only [(P₀ 2).huge,Nat.cast_nonneg (α:=ℝ) cap]
  have α:0<(P₀ 0).arc:=by linarith only [(P₀ 0).huge,Nat.cast_nonneg (α:=ℝ) cap]
  obtain ⟨t,spent⟩:=eventually_atTop.mp (mixed (P₀ 2).arc (P₀ 0).arc ea (fits P₀ c checks) x diff)
  obtain ⟨n,roll⟩:=eventually_atTop.mp (wheels R simple shop)
  refine ⟨w,Q,B 2,cap,P₀ 0,apart,Qpos,posB 2,?_⟩
  intro floor τ τpos τone
  filter_upwards [dates (max floor (max t n)) τ τpos] with ℓ earlier
  obtain ⟨k,start,prior,fee,⟨tab,program⟩,law⟩:=earlier
  obtain ⟨L,v,menu,active⟩:=program.supply 2
  have ready:Allowed (Lev) (P₀ 2).arc k:=by simpa only [(P₀ 2).factor] using menu.age.allot.permitted
  have joint:=spent k (by omega) ℓ prior (span R (fee.trans (Real.rpow_le_rpow_of_exponent_le ((Lev).fits.delayed ℓ).le τone))) ready (roll k (by omega))
  refine ⟨k,(le_max_left ..).trans start,prior,fee,?_⟩
  filter_upwards [law,joint] with N original hear
  obtain ⟨late,price⟩:=hear
  refine ⟨late,?_⟩
  intro p hk ξ matrix z V₀ r honest loc
  have main:0<gap (Lev) (P₀ 0).arc k:=mul_pos ((Rf).S.a_pos k) (Real.rpow_pos_of_pos (Real.exp_pos _) _)
  obtain ⟨u,rent,inv,good⟩:=(original p (prior.trans_lt late) 0).1 z V₀ r honest
  have rho:ξ.band=(P₀ 0).arc:=(P₀ 0).factor _
  let shifted:=fun i=>slide R hk (z i)
      (((Rf).S.toDepth hk p).parent (WilsonPositionPhysicalCellTest.site (R:=R) (gap (Lev) ξ.band k) (N,p) x i))
  have identical:loc=shifted:=by
    unfold shifted
    rw [rho]
    rfl
  refine ⟨u,rent,?_,?_,?_⟩
  · rw [identical]
    exact inv
  · rw [identical]
    exact good
  intro D' V j v hj station audit a
  obtain ⟨inside,root⟩:=(original p (prior.trans_lt late) 2).2 (z 1) (V₀ 1) (r 1) (honest 1) (u 1 a)
  rw [(P₀ 2).factor] at inside root
  let b:=lifts R (p:=p) hk (gap (Lev) (P₀ 0).arc k) main x
  have eq:∀i, WilsonThermometerWeakMovedCovers.move (Rf).S p hk (z i) (wrap _ (b i))=loc i:=
    WilsonThermometerWeakRankCovers.sites R hk _ main x z
  have costed:=price p z b (WilsonThermometerWeakRankCovers.coordinates R hk _ main x) V j v hj station audit (r 1) (u 1 a) _ inside root
  simpa only [eq] using costed
theorem original (simple:G.Simple) (paid:R2I.RG05Joint.AcrossPanels R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G) (W:Warehouse G)
    (μ ε:ℝ) (pos:0<ε) (f:Extraction.Order) (hier:(Cells.standard Rf).Hierarchy) :
    ∃(w:E4)(Q B:ℝ)(cap:ℕ)(exam:Panel cap), (0:E4)≠w ∧ 0≤Q ∧ 0<B ∧
    ∀floor:ℕ,∀ᶠ ℓ:ℕ in atTop,∃k:ℕ, floor≤k ∧ ∃prior:k≤ℓ, ∀ᶠ N:ℕ in atTop,∃late:ℓ<N,∀p,
      let hk:k≤N:=prior.trans late.le
      let ξ:=exam.bag ((Lev).clock.J k)
      let K:=MSDeckProbeGram.matrix M 4 0 w μ 0
      ∀ (z:Fin 2→Site ((Rf).side N p)) (V₀:Fin 2→Sight Rf 4 p) (r:Fin 2→Emblems Rf 4),
      (∀i,Enrolled R.makes R.doors cash k N p 4 (digits R N p (z i)) (V₀ i) (r i)) →
      let loc:=locations R hk w exam.arc z
      ∃u:Fin 2→Glyph C 4→(Rf).label 4,
      let y:=fun (i:Fin 2)(j:Glyph C 4)=>chunk (C:=Rf) (WilsonThermometerOwnOffsetField.primaryLetter 4) (u i j)
      let A:Matrix (Glyph C 4) (Glyph C 4) ℂ:=fun a e=>reading R (fun _=>4) loc (fun i=>y i (![a,e] i)) r hk full
      (∀i j,size (y i j)≤Perch.bill (ξ.credit-1) (clim (Lev) k)) ∧
      IsUnit A ∧ (∀i j,‖A⁻¹ i j-K⁻¹ i j‖<1) ∧
      ∀{D':ℕ}(V:Vane Rf D') (j:Fin (D'+1)) (v:(Cells.standard Rf).Field j),
      j.val=4 → V.k=ℓ → V.checked f hier D' → ∀a,
      ‖moment ((Rf).beta N p) (fun U=>(Rf).O N p (V.wheel.atCut (N,p) j v) (loc 0) U*arm R (r 1) hk (loc 1) (u 1 a) U)‖≤
      (Q*((Lev).clock.hatBeta ℓ)^ε*(cost (Rf) 4*‖v‖)) *
        (B*((2*scaleCost (Rf) 4)*((Rf).labels.level 4).coeffSize (u 1 a))) :=by
  obtain ⟨w,Q,B,cap,exam,away,hQ,hB,purchase⟩:=withSpan R M simple paid shop S W μ ε pos f hier
  refine ⟨w,Q,B,cap,exam,away,hQ,hB,?_⟩
  intro floor
  filter_upwards [purchase floor 1 zero_lt_one le_rfl] with ℓ event
  obtain ⟨k,start,later,_,taken⟩:=event
  exact ⟨k,start,later,taken⟩

end YM.Integration.WilsonThermometerWeakFourMixedRoster
end
