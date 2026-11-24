import YM.Integration.WilsonThermometerWeakWardRows
import YM.Integration.WilsonThermometerWeakFourMixedRoster

/-! Regulator-uniform election of the honest mixed physical price and the
separate two-cell equation on the very same filed axes at any finite grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakJointWardMenu
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

open WilsonThermometerWeakFourMixedRoster (locations)
open Push Next.Extract
def lodged {N p k d:ℕ} (hk:k≤N) (z:Fin 2→Site ((Rf).side N p))
    (r:Emblems Rf d) (u:Glyph C d→(Rf).label d) (B:ℝ) (radius:ℕ) :Prop:=
  ∃(m:ℕ)(hm:m≤k)(t:Site ((Rf).side N p))(v w:Site ((Rf).side m p)),
  let T:=center (Rf).S p (hm.trans hk) 0
  v≠w ∧ z 0+t∈T.margin v (3*span (Rf).S hk p) ∧
  ∀i, LocalOn (YM.Push.Mark.Outer radius (z 0+t)) (arm R r hk (z 1+t) (u i)) ∧
    ∃Y,Interior (T.chamber 0) Y ∧ T.rootTest ((Rf).beta N p) Y≤B*(((Rf).labels.level d).coeffSize (u i)) ∧
      T.copy w Y=arm R r hk (z 1+t) (u i)

private theorem growing {e h:ℕ} (le:e≤h) (a b:ℝ):WilsonThermometerWeakJointWidth.power a b e≤WilsonThermometerWeakJointWidth.power a b h:=by
  unfold WilsonThermometerWeakJointWidth.power
  gcongr
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

theorem original (d radius:ℕ) (simple:G.Simple) (paid:R2I.RG05Joint.AcrossPanels R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G) (W:Warehouse G)
    (μ ε:ℝ) (pos:0<ε) (f:Extraction.Order) (hier:(Cells.standard Rf).Hierarchy) :
    ∃(w:E4)(Q B:ℝ)(cap:ℕ)(exam:Panel cap), (0:E4)≠w ∧ 0≤Q ∧ 0<B ∧
    ∀(floor:ℕ)(τ:ℝ),0<τ → τ≤1 → ∀ᶠ ℓ:ℕ in atTop,∃k:ℕ, floor≤k ∧ ∃prior:k≤ℓ, (Rf).S.a k/(Rf).S.a ℓ≤(Lev).clock.hatBeta ℓ^τ ∧ ∀ᶠ N:ℕ in atTop,∃late:ℓ<N,∀p,
      let hk:k≤N:=prior.trans late.le
      let ξ:=exam.bag ((Lev).clock.J k)
      let K:=MSDeckProbeGram.matrix M d 0 w μ 0
      ∀ (z:Fin 2→Site ((Rf).side N p)) (V₀:Fin 2→Sight Rf d p) (r:Fin 2→Emblems Rf d),
      (∀i,Enrolled R.makes R.doors cash k N p d (digits R N p (z i)) (V₀ i) (r i)) →
      let loc:=locations R hk w exam.arc z
      ∃u:Fin 2→Glyph C d→(Rf).label d,
      let y:=fun (i:Fin 2)(j:Glyph C d)=>chunk (C:=Rf) (WilsonThermometerOwnOffsetField.primaryLetter d) (u i j)
      let A:Matrix (Glyph C d) (Glyph C d) ℂ:=fun a e=>reading R (fun _=>d) loc (fun i=>y i (![a,e] i)) r hk full
      (∀i j,size (y i j)≤Perch.bill (ξ.credit-1) (clim (Lev) k)) ∧
      IsUnit A ∧ (∀i j,‖A⁻¹ i j-K⁻¹ i j‖<1) ∧
      lodged R hk loc (r 1) (u 1) (B*(2*scaleCost (Rf) d)) radius ∧
      ∀{D':ℕ}(V:Vane Rf D') (j:Fin (D'+1)) (v:(Cells.standard Rf).Field j),
      j.val=d → V.k=ℓ → V.checked f hier D' → ∀a,
      ‖moment ((Rf).beta N p) (fun U=>(Rf).O N p (V.wheel.atCut (N,p) j v) (loc 0) U*arm R (r 1) hk (loc 1) (u 1 a) U)‖≤
      (Q*((Lev).clock.hatBeta ℓ)^ε*(cost (Rf) d*‖v‖)) *
        (B*((2*scaleCost (Rf) d)*((Rf).labels.level d).coeffSize (u 1 a))):=by
  let grade:Fin (d+1):=⟨d,Nat.lt_succ_self _⟩
  obtain ⟨P,κ,e,skyChecks,policy⟩:=WilsonThermometerWeakSameRunCross.original (d:=d) R simple shop
    paid f hier grade ε pos
  obtain ⟨Q,Qpos,mixed⟩:=policy 0
  have arc:0<(P 0).arc:=by linarith only [(P 0).huge]
  obtain ⟨e₁,housing⟩:=WilsonThermometerWeakWardChambers.original R simple shop
  obtain ⟨cap,depth,fits⟩:=WilsonThermometerWeakDisplacedHorizon.original (P 0).arc arc (max e e₁) d
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
  have room:=fits P₀ c checks
  have larger:=lt_of_le_of_lt (growing (le_max_left e e₁) _ _) room
  have enough:=lt_of_le_of_lt (growing (le_max_right e e₁) _ _) room
  obtain ⟨s,holds⟩:=eventually_atTop.mp (housing (P 0).arc (P₀ 2).arc (P₀ 0).arc arc ea enough x diff)
  obtain ⟨t,spent⟩:=eventually_atTop.mp (mixed (P₀ 2).arc (P₀ 0).arc ea larger x diff)
  obtain ⟨n,roll⟩:=eventually_atTop.mp (wheels R simple shop)
  refine ⟨w,Q,B 2,cap,P₀ 0,apart,Qpos,posB 2,?_⟩
  intro floor τ τpos τone
  filter_upwards [dates (max floor (max s (max t n))) τ τpos] with ℓ earlier
  obtain ⟨k,start,prior,fee,⟨tab,program⟩,law⟩:=earlier
  obtain ⟨L,v,menu,active⟩:=program.supply 2
  have ready:Allowed (Lev) (P₀ 2).arc k:=by simpa only [(P₀ 2).factor] using menu.age.allot.permitted
  have joint:=spent k (by omega) ℓ prior (span R (fee.trans (Real.rpow_le_rpow_of_exponent_le ((Lev).fits.delayed ℓ).le τone))) ready (roll k (by omega))
  refine ⟨k,(le_max_left ..).trans start,prior,fee,?_⟩
  filter_upwards [law,joint,holds k (by omega) ready (roll k (by omega)) d radius] with N original hear cabins
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
  let b:=lifts R (p:=p) hk (gap (Lev) (P₀ 0).arc k) main x
  have eq:∀i, WilsonThermometerWeakMovedCovers.move (Rf).S p hk (z i) (wrap _ (b i))=loc i:=
    WilsonThermometerWeakRankCovers.sites R hk _ main x z
  refine ⟨u,rent,?_,?_,?_,?_⟩
  · rw [identical]
    exact inv
  · rw [identical]
    exact good
  · obtain ⟨_,raw⟩:=cabins
    obtain ⟨m,hm,t,c₀,c₁,different,left,arms⟩:=raw p z b (WilsonThermometerWeakRankCovers.coordinates R hk _ main x)
    refine ⟨m,hm,t,c₀,c₁,different,?_,?_⟩
    · simpa only [eq] using left
    intro i
    obtain ⟨away,post⟩:=arms (r 1) (u 1 i)
    obtain ⟨inside,root⟩:=(original p (prior.trans_lt late) 2).2 (z 1) (V₀ 1) (r 1) (honest 1) (u 1 i)
    rw [(P₀ 2).factor] at inside root
    obtain ⟨Y,member,feeY,same⟩:=post _ inside root
    refine ⟨by simpa only [eq] using away,Y,member,?_,by simpa only [eq] using same⟩
    simpa only [mul_assoc] using feeY
  intro D' V j v hj station audit a
  obtain ⟨inside,root⟩:=(original p (prior.trans_lt late) 2).2 (z 1) (V₀ 1) (r 1) (honest 1) (u 1 a)
  rw [(P₀ 2).factor] at inside root
  have costed:=price p z b (WilsonThermometerWeakRankCovers.coordinates R hk _ main x) V j v hj station audit (r 1) (u 1 a) _ inside root
  simpa only [eq] using costed

end YM.Integration.WilsonThermometerWeakJointWardMenu
end
