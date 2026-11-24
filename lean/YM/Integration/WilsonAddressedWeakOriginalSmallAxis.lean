import YM.Integration.WilsonAddressedWeakSingletonRoot
import YM.Integration.WilsonThermometerWeakPanelAxes

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakOriginalSmallAxis
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

open Next.Rank Read Cells

open WilsonThermometerWeakPanelBorn

private theorem parent_origin {k N p:ℕ} (hk:k≤N) (ρ:ℝ) (w:E4):
    ((Rf).S.toDepth hk p).parent (WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) (Extra.FD.couple 0 w) 0)=0:=by
  let g:=(Rf).S.toDepth hk p
  have origin:WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) (Extra.FD.couple 0 w) 0=0:=by
    ext a
    change ((⌈ρ*(0:ℝ)/(Rf).S.a N⌉:ℤ):ZMod ((Rf).side N p).val)=0
    simp
  rw [origin]
  have zero:lift (0:Site g.count)=0:=by funext a;simp [Lattice.lift]
  have assembled:g.assemble (0,0)=0:=by
    change g.root 0+Lattice.wrap _ (lift (0:Site g.count))=0
    rw [map_zero,zero,map_zero,add_zero]
  change g.parent 0=0
  rw [←assembled,g.assemble_parent]

/-- One and the same inverse on the held Hail issues every numerical input axis.
The unsubtracted positive Wilson root at the centered physical copy stays bounded jointly in N,p. -/
theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G) (exam:Panel H)
    (grade:d≤H) (φ:Test 2) (separated:tsupport φ⊆generic 2) (w:E4) (apart:(0:E4)≠w)
    (near:tsupport φ∈𝓝 (Extra.FD.couple 0 w)) (B:Binding Rf) (J:ChartRatio G) (O:HaarBudget G):
    ∃ C:ℝ,0<C ∧ ∀ᶠ k:ℕ in atTop, ∀ᶠ N:ℕ in atTop, ∀ (p n:ℕ) (hk:k<N) (_:2≤n),
    let F:=(Rf).labels.level d;let ξ:=exam.bag ((Lev).clock.J k)
    let tile:=Ship.yard Rf ξ.band hk.le p;let β:=(Rf).beta N p
    ∀ (b l q:ℝ) (menu:LegacyCost B J (-3) b ξ k n H O l q) (Q:Rep G ((Rf).side k p)),
      (∀ j≤d,Accent.generator G j≤b) → Actum B R.makes O J exam menu Q hk →
    ∀ (z₀:Site ((Rf).side N p)) (V:Sight Rf d p) (r:Emblems Rf d),
      Enrolled R.makes R.doors cash k N p d (digits R N p z₀) V r →
      ∃ T:F.Coeff≃ₗ[ℂ]F.Coeff, (∀ all,F.coeffSize (T all)≤2*F.coeffSize all) ∧
        ∀ j:F.Index,
        let u:=WilsonThermometerWeakPanelExchange.refine Rf (Price.shrink Rf k N p)⁻¹ (mag (Lev) ξ.band k) T (Size.axis F j)
        let f:=arm R r hk.le (WilsonAddressedWeakFixedChild.slide R hk.le z₀ 0) u
        Interior (tile.chamber 0) f ∧ tile.rootTest β f≤C+Ship.budget (Lev) n k:=by
  let x₀:=Extra.FD.couple 0 w
  obtain ⟨C,c,hC,hc,smallMean⟩:=WilsonAddressedWeakSingletonRoot.axes R (d:=d) x₀ (Extra.FD.couple_ok apart)
  obtain ⟨t,ht,thick⟩:=φ.hasCompactSupport.exists_cthickening_subset_open (conf_open 2) φ.tsupport_subset
  let K₀:=cthickening t (tsupport φ)
  have compact:IsCompact K₀:=φ.hasCompactSupport.cthickening
  obtain ⟨rad,hr,ball⟩:=Metric.mem_nhds_iff.mp near
  have six:6≤exam.arc:=by linarith only [exam.huge,Nat.cast_nonneg (α:=ℝ) H]
  have pos:0<exam.arc:=by linarith only [six]
  let F:=(Rf).labels.level d
  have shrink:Tendsto (fun k=>(40:ℝ)*(mag (Lev) exam.arc k)⁻¹) atTop (𝓝 0):=by
    simpa only [mul_zero,Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp (mag_rate (Lev) simple pos)).const_mul 40
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_all.mpr (fun j:F.Index=>WilsonAddressedWeakPhysicalReceipt.original R simple shop S exam grade (fun _=>Size.axis F j) compact thick B J O),
    WilsonAddressedWeakPanelSpacing.original R simple φ exam.arc pos,
    WilsonAddressedWeakFiledTargets.fits R simple φ separated exam.arc pos,
    WilsonAddressedWeakStationRoom.original R simple φ exam.arc pos,
    shrink.eventually (gt_mem_nhds (lt_min hc (lt_min hr ht))),WilsonThermometerWeakPanelAxes.original R simple shop S exam grade]
    with k due spaced fit room near head
  let ξ:=exam.bag ((Lev).clock.J k);let χ:=width (Lev) ξ.band k
  have band:ξ.band=exam.arc:=exam.factor _
  rw [←band] at spaced fit room near
  let gr:χ≤k:=(wider (Lev) ξ.band k).trans (before ..)
  filter_upwards [WilsonAddressedWeakChamber.original R χ d] with N houses
  intro p n hk hn F' issued tile β b l q menu Q funds current z₀ V r hw
  let A:=(Rf).path.rep N p k;let E:AtlasData G (Rf).S p:=stamp (Lev) N p
  let ρ:=gap (Lev) ξ.band k
  have rpos:0<ρ:=gap_pos ..
  have ratio:(Rf).S.a k/ρ=(mag (Lev) ξ.band k)⁻¹:=by
    dsimp [ρ,ξ,gap];field_simp [(Lev).S.a_pos k |>.ne',(mag_pos (Lev) _ k).ne']
  have date:ξ.taylor+1≤A.p.order:=by
    have eq:A.p=(Lev).budget k:=(R.makes.wilson.represents N p k hk.le).vac
    exact eq.symm ▸ menu.moves.length
  obtain ⟨K,wide,post⟩:=head N p hk.le
  obtain ⟨T,forward,axes⟩:=post date z₀ V r hw E (current.pays.birth E rfl)
  refine ⟨T,forward,?_⟩
  obtain ⟨x,placed,distx⟩:=WilsonAddressedWeakFixedPlacement.original R hk.le ρ rpos x₀ (fun _=>z₀)
  rw [ratio] at distx
  have mp:0<(mag (Lev) ξ.band k)⁻¹:=inv_pos.mpr (mag_pos ..)
  have room₀:=near.trans_le (min_le_right ..)
  have dx:dist x x₀<rad:=by linarith only [distx,mp,room₀.trans_le (min_le_left ..)]
  have supp:x∈tsupport φ:=ball (Metric.mem_ball.mpr dx)
  let z:=WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
  let v:=projected R (p:=p) hk.le ρ rpos x
  have move:dist v x≤16*(mag (Lev) ξ.band k)⁻¹:=by simpa only [ratio] using (actual R (p:=p) hk.le ρ rpos x).2
  have atC:dist v x₀<c:=(dist_triangle v x x₀).trans_lt (by linarith only [move,distx,near.trans_le (min_le_left ..)])
  have enrolled (i:Fin 2):Enrolled R.makes R.doors cash k N p d (digits R N p (z i)) V r:=by
    change Enrolled R.makes R.doors cash k N p d (digits R N p (WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x i)) V r
    rw [placed];exact WilsonAddressedWeakFixedChild.enrolled R hk.le z₀ _ hw
  obtain ⟨Q₀,_,_,bounds⟩:=room menu.age.allot.permitted N p hk.le
  have admitted:=fit menu.age.allot.permitted N p hk.le x supp
  have same:tested (Lev) ξ.band k v=v:=(WilsonAddressedWeakMaxwellPositions.stations R (p:=p) hk.le ξ.band x).2.2
  have here:tested (Lev) ξ.band k v∈K₀:=by
    rw [same];apply Metric.mem_cthickening_of_dist_le _ x _ _ supp
    linarith only [move,mp,room₀.trans_le (min_le_right ..)]
  have origin: z 0=WilsonAddressedWeakFixedChild.slide R hk.le z₀ 0:=by
    change WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x 0=_
    rw [placed]
    exact congrArg (WilsonAddressedWeakFixedChild.slide R hk.le z₀) (parent_origin R hk.le ρ w)
  intro j u f
  obtain ⟨L,money,gross,sharp,degree,spirit,paid,healthy⟩:=axes j
  let y:=chunk (C:=Rf) (primaryLetter d) u
  let val:Fin 2→(Rf).label d:=fun _=>Size.axis F j
  let tags:=Atlas.jointX (C:=Rf) (d0:=fun _:Fin 2=>d) val
  let fs:=WilsonThermometerIntrinsicRoster.source R (fun _=>d) z (fun _=>y) (fun _=>r) hk.le
  have charged:=due j N p n hk hn x b l q menu Q funds current here admitted
    (spaced menu.age.allot.permitted N p hk x supp)
    (fun _=>V) (fun _=>r) (fun _=>y) enrolled (fun _=>K) (fun _=>L)
    (fun _=>money) (fun _=>spirit) (fun _=>gross) (fun _=>degree) (fun _=>sharp) wide (fun _=>paid) (fun _=>healthy)
  have ins:Interior (tile.chamber 0) (fs 0):=houses p (gr.trans hk.le) k hk.le (fun _=>d) (fun _=>le_rfl)
    ρ rpos x (bounds x supp).2.2.2 (fun _=>y) (fun _=>r) 0
  have actual:f=fs 0:=by
    change arm R r hk.le (WilsonAddressedWeakFixedChild.slide R hk.le z₀ 0) u=_
    rw [←origin,WilsonThermometerWeakPanelBorn.source];rfl
  rw [actual];refine ⟨ins,?_⟩
  have one:=WilsonAddressedWeakSingletonRoot.restored R ξ.band hk.le v admitted tags fs 0 ins
  have mean:=smallMean v atC j
  rw [same] at one
  have nonempty:(Next.Rank.Glyph.slot (0:Fin 2)).val.Nonempty:=by change ({(0:Fin 2)}:Finset _).Nonempty;simp
  have rhs:=add_le_add (charged (Next.Rank.Glyph.slot 0) nonempty) mean
  exact one.trans (rhs.trans_eq (add_comm ..))
end YM.Integration.WilsonAddressedWeakOriginalSmallAxis
end
