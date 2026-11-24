import YM.Integration.WilsonAddressedWeakCommonAxes
import YM.Integration.WilsonAddressedWeakFixedPlacement
import YM.Integration.WilsonAddressedWeakDetectorExpense
import YM.Integration.WilsonAddressedWeakStationGram

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakFixedObservation
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

/-- The unsigned physical product is heard after the two singleton subtractions on the original
finite Wilson law. The own residues and the calibrated fields are common to every matrix entry. -/
theorem coordinates (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G) (exam:Panel H)
    (grade:d≤H) (φ:Test 2) (separated:tsupport φ⊆generic 2) (x₀:Points 2) (near:tsupport φ∈𝓝 x₀)
    (μ:ℝ) (B:Binding Rf) (J:ChartRatio G) (O:HaarBudget G):
    ∃ A:ℝ,0<A ∧ ∀ᶠ k:ℕ in atTop, ∀ᶠ N:ℕ in atTop, ∀ (p n:ℕ) (hk:k<N) (_:2≤n),
    let s:=clim (Lev) k;let ξ:=exam.bag ((Lev).clock.J k)
    let ρ:=gap (Lev) ξ.band k;let g:=(Rf).S.toDepth hk.le p
    ∀ (b l q:ℝ) (menu:LegacyCost B J (-3) b ξ k n H O l q) (Q:Rep G ((Rf).side k p)),
      (∀ j≤d,Accent.generator G j≤b) → Actum B R.makes O J exam menu Q hk →
    ∀ (z₀:Fin 2→Site ((Rf).side N p)) (V:Fin 2→Sight Rf d p) (r:Fin 2→Emblems Rf d),
      (∀ i,Enrolled R.makes R.doors cash k N p d (digits R N p (z₀ i)) (V i) (r i)) →
      ∃ u:Fin 2→Glyph C d→(Rf).label d,
      let y:=fun (i:Fin 2)(j:Glyph C d)=>chunk (C:=Rf) (WilsonThermometerOwnOffsetField.primaryLetter d) (u i j); (∀ i j,size (y i j)≤Perch.bill (ξ.credit-1) s) ∧
      ∃ x:Points 2,
        let z:=WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
        let v:=projected R (p:=p) hk.le ρ (gap_pos ..) x
        z=(fun i=>WilsonAddressedWeakFixedChild.slide R hk.le (z₀ i)
          (g.parent (WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x₀ i))) ∧
        dist v x₀≤40*(mag (Lev) ξ.band k)⁻¹ ∧
        ∀ a e:Glyph C d,
          ‖reading R (fun _=>d) z (fun i=>y i (![a,e] i)) r hk.le full -
              MSDeckProbeGram.raw M ![a,e] v μ 0‖≤(1+2*A)*Ship.budget (Lev) n k:=by
  obtain ⟨A,hA,caps⟩:=WilsonAddressedWeakShapeFees.proper (D:=d) M φ μ
  obtain ⟨rad,hr,ball⟩:=Metric.mem_nhds_iff.mp near
  have pos:0<exam.arc:=by linarith only [exam.huge,Nat.cast_nonneg (α:=ℝ) H]
  have shrink:Tendsto (fun k=>(24:ℝ)*(mag (Lev) exam.arc k)⁻¹) atTop (𝓝 0):=by
    simpa only [mul_zero,Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp (mag_rate (Lev) simple pos)).const_mul 24
  refine ⟨A,hA,?_⟩
  filter_upwards [WilsonAddressedWeakCommonAxes.coordinates R simple shop S exam grade (representatives R C (d:=d))
      φ separated B J O, WilsonAddressedWeakStationRoom.original R simple φ exam.arc pos,
      shrink.eventually (gt_mem_nhds (lt_min hr zero_lt_one))] with k axes room small
  let ξ:=exam.bag ((Lev).clock.J k)
  have band:ξ.band=exam.arc:=exam.factor _
  rw [←band] at room small
  let χ:=width (Lev) ξ.band k
  let gr:χ≤k:=(wider (Lev) ξ.band k).trans (before ..)
  filter_upwards [WilsonAddressedWeakChamber.original R χ d] with N houses
  intro p n hk hn s issued ρ g b l q menu Q funds current z₀ V r enrolled
  have rpos:0<ρ:=gap_pos ..
  have ratio:(Rf).S.a k/ρ=(mag (Lev) ξ.band k)⁻¹:=by
    dsimp [ρ,issued,ξ,gap];field_simp [(Lev).S.a_pos k |>.ne',(mag_pos (Lev) ξ.band k).ne']
  obtain ⟨u,money,table⟩:=axes N p n hk hn b l q menu Q funds current z₀ V r enrolled
  let y:=fun (i:Fin 2)(j:Glyph C d)=>chunk (C:=Rf) (WilsonThermometerOwnOffsetField.primaryLetter d) (u i j)
  obtain ⟨x,hx,distx⟩:=WilsonAddressedWeakFixedPlacement.original R hk.le ρ rpos x₀ z₀
  rw [ratio] at distx
  have supp:x∈tsupport φ:=ball (Metric.mem_ball.mpr (distx.trans_lt (small.trans_le (min_le_left ..))))
  let z:=WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
  let v:=projected R (p:=p) hk.le ρ rpos x
  have inc (i:Fin 2):Enrolled R.makes R.doors cash k N p d (digits R N p (z i)) (V i) (r i):=by
    change Enrolled R.makes R.doors cash k N p d (digits R N p (WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x i)) _ _
    rw [hx]
    exact WilsonAddressedWeakFixedChild.enrolled R hk.le (z₀ i) _ (enrolled i)
  obtain ⟨fit,price⟩:=table x supp inc
  have moved:dist v x≤16*(mag (Lev) ξ.band k)⁻¹:=by simpa only [ratio] using (actual R (p:=p) hk.le ρ rpos x).2
  refine ⟨u,money,x,hx,(dist_triangle v x x₀).trans ((add_le_add moved distx).trans_eq (by ring)),?_⟩
  intro a e
  let Y (i:Fin 2):=y i (![a,e] i)
  let mean (i:Fin 2):=WilsonAddressedWeakShapeFees.mean M (![a,e] i) v i μ
  let raw:=MSDeckProbeGram.raw M ![a,e] v μ 0
  let δ:=Ship.budget (Lev) n k
  have small1:dist v x≤1:=by
    have mpos:0<(mag (Lev) ξ.band k)⁻¹:=inv_pos.mpr (mag_pos ..)
    have :=small.trans_le (min_le_right ..); linarith only [moved,this,mpos]
  have bound (i:Fin 2): ‖mean i‖≤A :=
    caps v (Metric.mem_cthickening_of_dist_le v x 1 (tsupport φ) supp small1) (![a,e] i) i
  let fee:=WilsonAddressedWeakRankHearing.fee R M (p:=p) gr hk.le le_rfl (fun _=>d) ρ rpos x a e μ Y r
  have paid (m:Finset (Fin 2)) (hm:m.Nonempty): fee m≤δ:=by
    change WilsonAddressedWeakRankHearing.fee R M (p:=p) gr hk.le le_rfl _ ρ rpos x a e μ Y r m≤δ
    rw [WilsonAddressedWeakDetectorExpense.original R M ξ.band hk.le le_rfl _ x a e μ Y r m hm fit]
    have eq:=projected_tags R (![a,e]:Fin 2→Glyph C d)
    have h:=price (![a,e]:Fin 2→Glyph C d) (scene m) hm
    unfold Atlas.jointX at h
    simpa only [Function.comp_apply,eq] using h
  obtain ⟨Q₀,_,_,places⟩:=room menu.age.allot.permitted N p hk.le
  have together:‖reading R (fun _=>d) z Y r hk.le full-raw‖≤fee {0,1}+‖mean 1‖*fee {0}+‖mean 0‖*fee {1}:=
    WilsonAddressedWeakCompensatedHearing.original R gr hk.le (fun _=>d) z Y r mean raw le_rfl
      (houses p (gr.trans hk.le) k hk.le (fun _=>d) (fun _=>le_rfl) ρ rpos x (places x supp).2.2.2 Y r)
  have nonneg (m:Finset (Fin 2)):0≤fee m:=by dsimp [fee,WilsonAddressedWeakRankHearing.fee];positivity
  refine together.trans ?_
  calc _≤δ+A*δ+A*δ:=
          add_le_add (add_le_add (paid {0,1} (by simp))
              (mul_le_mul (bound 1) (paid {0} (by simp)) (nonneg _) hA.le))
            (mul_le_mul (bound 0) (paid {1} (by simp)) (nonneg _) hA.le)
       _=(1+2*A)*δ:=by ring

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G) (exam:Panel H)
    (grade:d≤H) (φ:Test 2) (separated:tsupport φ⊆generic 2) (x₀:Points 2) (near:tsupport φ∈𝓝 x₀)
    (μ:ℝ) (B:Binding Rf) (J:ChartRatio G) (O:HaarBudget G):
    ∃ A:ℝ,0<A ∧ ∀ᶠ k:ℕ in atTop, ∀ᶠ N:ℕ in atTop, ∀ (p n:ℕ) (hk:k<N) (_:2≤n),
    let s:=clim (Lev) k;let ξ:=exam.bag ((Lev).clock.J k)
    let ρ:=gap (Lev) ξ.band k;let g:=(Rf).S.toDepth hk.le p
    ∀ (b l q:ℝ) (menu:LegacyCost B J (-3) b ξ k n H O l q) (Q:Rep G ((Rf).side k p)),
      (∀ j≤d,Accent.generator G j≤b) → Actum B R.makes O J exam menu Q hk →
    ∀ (z₀:Fin 2→Site ((Rf).side N p)) (V:Fin 2→Sight Rf d p) (r:Fin 2→Emblems Rf d),
      (∀ i,Enrolled R.makes R.doors cash k N p d (digits R N p (z₀ i)) (V i) (r i)) →
      ∃ y:Fin 2→Glyph C d→Palette Rf d, (∀ i j,size (y i j)≤Perch.bill (ξ.credit-1) s) ∧
      ∃ x:Points 2,
        let z:=WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
        let v:=projected R (p:=p) hk.le ρ (gap_pos ..) x
        z=(fun i=>WilsonAddressedWeakFixedChild.slide R hk.le (z₀ i)
          (g.parent (WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x₀ i))) ∧
        dist v x₀≤40*(mag (Lev) ξ.band k)⁻¹ ∧
        ∀ a e:Glyph C d,
          ‖reading R (fun _=>d) z (fun i=>y i (![a,e] i)) r hk.le full -
              MSDeckProbeGram.raw M ![a,e] v μ 0‖≤(1+2*A)*Ship.budget (Lev) n k:=by
  obtain ⟨A,hA,rows⟩:=coordinates R M simple shop S exam grade φ separated x₀ near μ B J O
  refine ⟨A,hA,?_⟩
  filter_upwards [rows] with k rows;filter_upwards [rows] with N rows
  intro p n hk hn s ξ ρ g b l q menu Q funds current z₀ V r enrolled
  obtain ⟨u,done⟩:=rows p n hk hn b l q menu Q funds current z₀ V r enrolled
  exact ⟨fun (i:Fin 2)(j:Glyph C d)=>chunk (C:=Rf) (WilsonThermometerOwnOffsetField.primaryLetter d) (u i j),done⟩

end YM.Integration.WilsonAddressedWeakFixedObservation
end
