import YM.Integration.WilsonAddressedWeakFiledTargets

/-! A fixed compact detector at the selected weak station, before either physical regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakStationGram
open Filter Function Set MeasureTheory Metric Lattice Wilson RG Source Cells RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox PhysicalNext.Repeat.Legato
open MergeProof Accent Motion Bandage Extra.Multi Menu
open FVA2 FVA2.ColorCode Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone
open Extraction Table Spec OPE OPE.Orbits PhysMS XSpace XSpace.Normalize Trace Trace.Pilot
open WilsonThermometerOffsetTrajectory WilsonAddressedWeakPointCells
open WilsonAddressedWeakCalibration WilsonAddressedWeakCorrectedCylinder
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G) {B:Local.Physical.Deck G} {O:Booked B} (M:MS_Data G O)
open Next.Rank Next.Rank.Station
open WilsonAddressedWeakRankHearing
local notation "A!"=>R.family.path.levels
set_option quotPrecheck false

/-- One actual nondegenerate orientation supports a detector satisfying every fine-axis clearance. -/
theorem direction : ∃ v:E4, (0:E4)≠v ∧ Extra.FD.couple 0 v∈generic 2 := by
  let v:E4 := WithLp.toLp 2 (fun _:Axis=>(1:ℝ))
  have different : (0:E4)≠v := by
    intro e
    have j:=congrArg (fun x:E4=>x (0:Axis)) e
    exact zero_ne_one (show (0:ℝ)=1 from j)
  refine ⟨v,different,?_⟩
  intro j i l z
  fin_cases i <;> fin_cases l <;> first | rfl | exact (zero_ne_one z).elim | exact (one_ne_zero z).elim

theorem original (simple:G.Simple) (V:Warehouse G) (D:ℕ) (μ:ℝ) {v:E4} (away:(0:E4)≠v)
    (realSites:Extra.FD.couple 0 v ∈ generic 2)
    (room:Set (Points 2)) (near:room∈𝓝 (Extra.FD.couple 0 v)) (ε:ℝ) (hp:0<ε) :
    ∃ (φ:Test 2) (δ:ℝ),tsupport φ⊆room ∩ generic 2 ∧ (∫x,φ x)=1 ∧ 0<δ ∧
      let K:=MSSeparatedTestGram.matrix M D μ 0 φ
      IsUnit K ∧ ∀ b:ℝ, 0<b → ∀ᶠ k:ℕ in atTop, Station.Allowed (A!) b k →
      let ρ:=Station.gap (A!) b k
      let χ:=Station.width (A!) b k
      let gr:χ≤k:=(Station.wider (A!) b k).trans (Station.before ..)
      ∀ᶠ N:ℕ in atTop,∀ p (live:k≤N) (d:Fin 2→ℕ) (_:∀i,d i≤D) (j:ℕ) (hj:j≤N)
        (Y:Glyph B D→Glyph B D→PointSites R N p→(i:Fin 2)→Palette R.family (d i))
        (U:Glyph B D→Glyph B D→PointSites R N p→(i:Fin 2)→Emblems R.family (d i)),
        (∀a b₁ x,φ x≠0 →
          let o:=WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
          ∀s:Finset (Fin 2), s.Nonempty →
            WilsonAddressedWeakRankHearing.fee R M (p:=p) gr live hj d ρ (gap_pos ..) x a b₁ μ (Y a b₁ o) (U a b₁ o) s≤δ) →
        let A:=WilsonAddressedWeakPointGram.measured R d live Y U full φ ρ
        IsUnit A ∧ ∀a b₁,‖A⁻¹ a b₁-K⁻¹ a b₁‖<ε := by
  obtain ⟨φ,η,c,hs,hm,hη,hc,rank,hear⟩ :=
    WilsonAddressedWeakCalibration.original R M V D μ away (room ∩ generic 2)
      (inter_mem near ((genericOpen 2).mem_nhds realSites)) ε hp
  obtain ⟨C,hC,cap⟩:=WilsonAddressedWeakShapeFees.proper M (D:=D) φ μ
  let δ:=η/(1+2*C)
  have hδ:0<δ:=div_pos hη (by positivity)
  refine ⟨φ,δ,hs,hm,hδ,rank,?_⟩
  intro b₀ positive
  have shrink:Tendsto (fun k=>(16:ℝ)*(mag (A!) b₀ k)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp (mag_rate (A!) simple positive)).const_mul 16
  filter_upwards [WilsonAddressedWeakStationRoom.original R simple φ b₀ positive,
      shrink.eventually (gt_mem_nhds (lt_min hc zero_lt_one))] with k houses small
  intro allowed
  let χ:=width (A!) b₀ k
  let gr:χ≤k:=(wider (A!) b₀ k).trans (before ..)
  let ρ:=gap (A!) b₀ k
  have hr:0<ρ:=gap_pos ..
  have ratio:R.family.S.a k/ρ=(mag (A!) b₀ k)⁻¹ := by
    dsimp [ρ,gap];field_simp [(A!).S.a_pos k |>.ne', (mag_pos (A!) b₀ k).ne']
  have calibrated : 16*(R.family.S.a k/ρ) < min c 1 := by simpa only [ratio] using small
  filter_upwards [WilsonAddressedWeakChamber.original R χ D] with N interiors
  intro p live d hd j hj Y U pay
  obtain ⟨Q,distance,margin,fits⟩:= houses allowed N p live
  apply hear d k N p live Y U full ρ hr (calibrated.trans_le (min_le_left ..))
  intro a b x hx
  let o:=WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
  let t:=projected R (p:=p) live ρ hr x
  let m (i:Fin 2) := WilsonAddressedWeakShapeFees.mean M (![a,b] i) t i μ
  let q:=MSDeckProbeGram.raw M ![a,b] t μ 0
  have ht:t∈cthickening 1 (tsupport φ) := mem_cthickening_of_dist_le t x 1 (tsupport φ)
    (subset_tsupport _ (mem_support.mpr hx))
    (((actual R (p:=p) live ρ hr x).2.trans calibrated.le).trans (min_le_right ..))
  have bounded (i:Fin 2): ‖m i‖≤C := cap t ht (![a,b] i) i
  let price:=WilsonAddressedWeakRankHearing.fee R M (p:=p) gr live hj d ρ hr x a b μ (Y a b o) (U a b o)
  have priced (s:Finset (Fin 2)) (hs:s.Nonempty) : price s≤δ := pay a b x hx s hs
  have combine : ‖reading R d o (Y a b o) (U a b o) live full-q‖ ≤
      price {0,1}+‖m 1‖*price {0}+‖m 0‖*price {1} :=
    WilsonAddressedWeakCompensatedHearing.original R gr live d o (Y a b o) (U a b o) m q hj
      (interiors p (gr.trans live) k live d hd ρ hr x
        (fits x (subset_tsupport _ (mem_support.mpr hx))).2.2.2 (Y a b o) (U a b o))
  refine combine.trans ?_
  calc
    _ ≤ δ+C*δ+C*δ := add_le_add (add_le_add (priced {0,1} (by simp))
      (mul_le_mul (bounded 1) (priced {0} (by simp)) (by dsimp [price,WilsonAddressedWeakRankHearing.fee];positivity) hC.le))
      (mul_le_mul (bounded 0) (priced {1} (by simp)) (by dsimp [price,WilsonAddressedWeakRankHearing.fee];positivity) hC.le)
    _ = η := by dsimp [δ];field_simp [show 1+2*C≠0 by positivity];ring

end YM.Integration.WilsonAddressedWeakStationGram
