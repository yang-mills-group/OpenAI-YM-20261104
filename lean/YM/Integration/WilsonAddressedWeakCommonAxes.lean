import YM.Integration.WilsonAddressedWeakPhysicalReceipt
import YM.Integration.WilsonAddressedWeakPanelSpacing
import YM.Integration.WilsonAddressedWeakFiledSalary
import YM.Integration.WilsonAddressedWeakFiledTargets

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakCommonAxes
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
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} (R:Run G) {d H:ℕ}
local notation "Rf" => R.family
local notation "Lev" => R.family.path.levels
local notation "cash" => WilsonThermometerOffsetLedger.cash R

/-- File a finite set of genuine weak columns on each original, individually addressed arm before
choosing its companion or sampling a translated copy. One filed y,L is used in every pairing. -/
theorem coordinates (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G) (exam:Panel H)
    (grade:d≤H) {J₀:Type} [Fintype J₀] (val:J₀→(Rf).label d) (φ:Test 2) (separated:tsupport φ⊆generic 2)
    (B:Binding Rf) (J:ChartRatio G) (O:HaarBudget G):
    ∀ᶠ k:ℕ in atTop,∀ (N p n:ℕ) (hk:k<N) (_:2≤n),
    let s:=clim (Lev) k;let ξ:=exam.bag ((Lev).clock.J k)
    let ρ:=gap (Lev) ξ.band k;let T:=Ship.yard Rf ξ.band hk.le p
    ∀ (b l q:ℝ) (menu:LegacyCost B J (-3) b ξ k n H O l q) (Q:Rep G ((Rf).side k p)),
      (∀ j≤d,Accent.generator G j≤b) → Actum B R.makes O J exam menu Q hk →
    ∀ (z₀:Fin 2→Site ((Rf).side N p)) (V:Fin 2→Sight Rf d p) (r:Fin 2→Emblems Rf d),
      (∀ i,Enrolled R.makes R.doors cash k N p d (digits R N p (z₀ i)) (V i) (r i)) →
      ∃ u:Fin 2→J₀→(Rf).label d,
      let y:=fun (i:Fin 2)(j:J₀)=>chunk (C:=Rf) (WilsonThermometerOwnOffsetField.primaryLetter d) (u i j);
      (∀ i j,size (y i j)≤Perch.bill (ξ.credit-1) s) ∧
      ∀ x∈tsupport φ,
        let z:=WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
        let v:=projected R (p:=p) hk.le ρ (gap_pos ..) x
        (∀ i,Enrolled R.makes R.doors cash k N p d (digits R N p (z i)) (V i) (r i)) →
        ∃ fit:Fit (Lev) ξ.band k v,∀ (mark:Fin 2→J₀) (m:modes (Fin 2)),m.val.Nonempty →
          T.rootTest ((Rf).beta N p) (fun U=>(Read.cylinder (Ship.targets Rf (Atlas.jointX (d0:=fun _:Fin 2=>d) (val ∘ mark)) fit)
            (WilsonThermometerIntrinsicRoster.source R (fun _=>d) z (fun i=>y i (mark i)) r hk.le) U).part m)
            ≤Ship.budget (Lev) n k:=by
  obtain ⟨t,ht,thick⟩:=φ.hasCompactSupport.exists_cthickening_subset_open (conf_open 2) φ.tsupport_subset
  let K₀:=cthickening t (tsupport φ)
  have compact:IsCompact K₀:=φ.hasCompactSupport.cthickening
  have six:6≤exam.arc:=by linarith only [exam.huge,Nat.cast_nonneg (α:=ℝ) H]
  have pos:0<exam.arc:=by linarith
  have shrink:Tendsto (fun k=>(16:ℝ)*(Station.mag (Lev) exam.arc k)⁻¹) atTop (𝓝 0):=by
    simpa only [mul_zero,Function.comp_apply] using (tendsto_inv_atTop_zero.comp (mag_rate (Lev) simple pos)).const_mul 16
  filter_upwards [eventually_all.mpr (fun mark:Fin 2→J₀=>WilsonAddressedWeakPhysicalReceipt.original R simple shop S exam grade (val ∘ mark) compact thick B J O),
    WilsonAddressedWeakPanelSpacing.original R simple φ exam.arc pos,WilsonAddressedWeakFiledTargets.fits R simple φ separated exam.arc pos,
    shrink.eventually (eventually_lt_nhds ht),eventually_all.mpr (fun j=>WilsonAddressedWeakFiledSalary.original R simple shop S exam grade (val j))]
    with k charged spacing fits nearby salaries
  intro N p n hk hn s ξ ρ T b l q menu Q funds current z₀ V r enrolled
  let A:=(Rf).path.rep N p k
  let Y:AtlasData G (Rf).S p:=stamp (Lev) N p
  have band:ξ.band=exam.arc:=exam.factor _
  rw [←band] at spacing fits nearby
  have date:ξ.taylor+1≤A.p.order:=by
    have eq:A.p=(Lev).budget k:=(R.makes.wilson.represents N p k hk.le).vac
    exact eq.symm ▸ menu.moves.length
  choose K wide publish using fun j=>salaries j N p hk.le
  choose u L wages using fun (i:Fin 2) j=>publish j date (z₀ i) (V i) (r i) (enrolled i) Y (current.pays.birth Y rfl)
  let y (i:Fin 2)(j:J₀):=chunk (C:=Rf) (primaryLetter d) (u i j)
  refine ⟨u,fun i j=>(wages i j).1,?_⟩
  intro x hx z v incoming
  have suited:=fits menu.age.allot.permitted N p hk.le x hx
  refine ⟨suited,?_⟩
  have actualDist:dist v x≤16*(mag (Lev) ξ.band k)⁻¹:=by
    have h:=(actual R (p:=p) hk.le ρ (gap_pos ..) x).2
    have a:(Rf).S.a k/ρ=(mag (Lev) ξ.band k)⁻¹:=by
      dsimp [ρ,gap];field_simp [(Lev).S.a_pos k |>.ne',(mag_pos (Lev) ξ.band k).ne']
    simpa only [a] using h
  have tst:tested (Lev) ξ.band k v∈K₀:=by
    rw [(WilsonAddressedWeakMaxwellPositions.stations R (p:=p) hk.le ξ.band x).2.2]
    exact mem_cthickening_of_dist_le v x t (tsupport φ) hx (actualDist.trans nearby.le)
  intro mark
  have proof:=charged mark N p n hk hn x b l q menu Q funds current tst suited
    (spacing menu.age.allot.permitted N p hk x hx)
    V r (fun j=>y j (mark j)) incoming
    (fun j=>K (mark j)) (fun j=>L j (mark j)) (fun j=>(wages j (mark j)).1) (fun j=>(wages j (mark j)).2.2.2.2.1)
    (fun j=>(wages j (mark j)).2.1) (fun j=>(wages j (mark j)).2.2.2.1) (fun j=>(wages j (mark j)).2.2.1)
    (wide (mark 0)) (fun j=>(wages j (mark j)).2.2.2.2.2.1) (fun j=>(wages j (mark j)).2.2.2.2.2.2)
  exact proof

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G) (exam:Panel H)
    (grade:d≤H) {J₀:Type} [Fintype J₀] (val:J₀→(Rf).label d) (φ:Test 2) (separated:tsupport φ⊆generic 2)
    (B:Binding Rf) (J:ChartRatio G) (O:HaarBudget G):
    ∀ᶠ k:ℕ in atTop,∀ (N p n:ℕ) (hk:k<N) (_:2≤n),
    let s:=clim (Lev) k;let ξ:=exam.bag ((Lev).clock.J k)
    let ρ:=gap (Lev) ξ.band k;let T:=Ship.yard Rf ξ.band hk.le p
    ∀ (b l q:ℝ) (menu:LegacyCost B J (-3) b ξ k n H O l q) (Q:Rep G ((Rf).side k p)),
      (∀ j≤d,Accent.generator G j≤b) → Actum B R.makes O J exam menu Q hk →
    ∀ (z₀:Fin 2→Site ((Rf).side N p)) (V:Fin 2→Sight Rf d p) (r:Fin 2→Emblems Rf d),
      (∀ i,Enrolled R.makes R.doors cash k N p d (digits R N p (z₀ i)) (V i) (r i)) →
      ∃ y:Fin 2→J₀→Palette Rf d,
      (∀ i j,size (y i j)≤Perch.bill (ξ.credit-1) s) ∧
      ∀ x∈tsupport φ,
        let z:=WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
        let v:=projected R (p:=p) hk.le ρ (gap_pos ..) x
        (∀ i,Enrolled R.makes R.doors cash k N p d (digits R N p (z i)) (V i) (r i)) →
        ∃ fit:Fit (Lev) ξ.band k v,∀ (mark:Fin 2→J₀) (m:modes (Fin 2)),m.val.Nonempty →
          T.rootTest ((Rf).beta N p) (fun U=>(Read.cylinder (Ship.targets Rf (Atlas.jointX (d0:=fun _:Fin 2=>d) (val ∘ mark)) fit)
            (WilsonThermometerIntrinsicRoster.source R (fun _=>d) z (fun i=>y i (mark i)) r hk.le) U).part m)
            ≤Ship.budget (Lev) n k:=by
  filter_upwards [coordinates R simple shop S exam grade val φ separated B J O] with k rows
  intro N p n hk hn s ξ ρ T b l q menu Q funds current z₀ V r enrolled
  obtain ⟨u,done⟩:=rows N p n hk hn b l q menu Q funds current z₀ V r enrolled
  exact ⟨fun (i:Fin 2)(j:J₀)=>chunk (C:=Rf) (WilsonThermometerOwnOffsetField.primaryLetter d) (u i j),done⟩

end YM.Integration.WilsonAddressedWeakCommonAxes
end
