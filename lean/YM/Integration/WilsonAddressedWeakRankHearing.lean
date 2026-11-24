import YM.Integration.WilsonAddressedWeakShapeFees

/-! Fixed original reflected accuracy for the inverse of the displaced physical detector at its own reporting date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakRankHearing
open Filter Function Set MeasureTheory Metric Lattice Wilson RG Source Cells RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox PhysicalNext.Repeat.Legato
open MergeProof Accent Motion Bandage Extra.Multi Menu
open FVA2 FVA2.ColorCode Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone
open Extraction Table Spec OPE OPE.Orbits PhysMS XSpace XSpace.Normalize Trace Trace.Pilot
open WilsonThermometerOffsetTrajectory WilsonAddressedWeakPointCells
open WilsonAddressedWeakCalibration WilsonAddressedWeakCorrectedCylinder
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G) {B:Local.Physical.Deck G} {O:Booked B} (M:MS_Data G O)
variable {D χ k N p j:ℕ}

def fee (gr:χ≤k) (live:k≤N) (hj:j≤N) (d:Fin 2→ℕ) (ρ:ℝ) (hr:0<ρ) (x:Points 2)
    (a b:Glyph B D) (μ:ℝ) (Y:(i:Fin 2)→Palette R.family (d i))
    (r:(i:Fin 2)→Emblems R.family (d i)) (s:Finset (Fin 2)) : ℝ :=
  let o := WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
  let t := projected R (p:=p) live ρ hr x
  let m (i:Fin 2) := WilsonAddressedWeakShapeFees.mean M (![a,b] i) t i μ
  let q := MSDeckProbeGram.raw M ![a,b] t μ 0
  ‖WilsonAddressedWeakCompensatedHearing.report R gr live d o Y r m q hj s‖^(Fintype.card (Site (R.family.side χ p)):ℝ)⁻¹

/-- The same three original signed prices at one determined numerical precision suffice for the full determinant. -/
theorem original (V:Warehouse G) (D:ℕ) (μ:ℝ) {v:E4} (away:(0:E4)≠v)
    (room:Set (Points 2)) (near:room ∈ 𝓝 (Extra.FD.couple 0 v)) (ε:ℝ) (hp:0<ε) :
    ∃ (φ:Test 2) (δ c:ℝ),tsupport φ⊆room ∧ (∫ x,φ x)=1 ∧ 0<δ ∧ 0<c ∧
    let K:=MSSeparatedTestGram.matrix M D μ 0 φ
    IsUnit K ∧ ∀ χ:ℕ,∃ ρ₀:ℝ,0<ρ₀ ∧ ∀ᶠ N:ℕ in atTop,
      ∀ p k (gr:χ≤k) (live:k≤N) (d:Fin 2→ℕ) (_:∀ i,d i≤D) (j:ℕ) (hj:j≤N)
        (Y:Glyph B D→Glyph B D→PointSites R N p→(i:Fin 2)→Palette R.family (d i))
        (U:Glyph B D→Glyph B D→PointSites R N p→(i:Fin 2)→Emblems R.family (d i))
        (ρ:ℝ) (hr:0<ρ),ρ≤ρ₀ → 16*(R.family.S.a k/ρ)<c →
        (∀ (a b:Glyph B D) (x:Points 2),φ x≠0 →
          let o:=WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
          ∀ s:Finset (Fin 2),s.Nonempty →
          fee R M (p:=p) gr live hj d ρ hr x a b μ (Y a b o) (U a b o) s≤δ) →
        let A:=WilsonAddressedWeakPointGram.measured R d live Y U full φ ρ
        IsUnit A ∧ ∀ a b,‖A⁻¹ a b-K⁻¹ a b‖<ε := by
  obtain ⟨φ,η,c,hs,hm,hη,hc,rank,hear⟩ :=
    WilsonAddressedWeakCalibration.original R M V D μ away room near ε hp
  obtain ⟨C,hC,cap⟩ := WilsonAddressedWeakShapeFees.proper M (D:=D) φ μ
  let δ:=η/(1+2*C)
  have hδ:0<δ := div_pos hη (by positivity)
  refine ⟨φ,δ,min c 1,hs,hm,hδ,lt_min hc zero_lt_one,rank,?_⟩
  intro χ
  obtain ⟨ρ₀,hr₀,fitted⟩:=WilsonAddressedWeakShapeFees.chamber R D χ φ
  refine ⟨ρ₀,hr₀,?_⟩
  filter_upwards [fitted] with N house
  intro p k gr live d hd j hj Y U ρ hr small gap pay
  apply hear d k N p live Y U full ρ hr (gap.trans_le (min_le_left ..))
  intro a b x hx
  let o:=WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
  let t:=projected R (p:=p) live ρ hr x
  let m (i:Fin 2) := WilsonAddressedWeakShapeFees.mean M (![a,b] i) t i μ
  let q:=MSDeckProbeGram.raw M ![a,b] t μ 0
  have ht:t∈cthickening 1 (tsupport φ) := mem_cthickening_of_dist_le t x 1 (tsupport φ)
    (subset_tsupport _ (mem_support.mpr hx))
    (((actual R (p:=p) live ρ hr x).2.trans gap.le).trans (min_le_right ..))
  have bounded (i:Fin 2): ‖m i‖≤C := cap t ht (![a,b] i) i
  let price:=fee R M (p:=p) gr live hj d ρ hr x a b μ (Y a b o) (U a b o)
  have priced (s:Finset (Fin 2)) (hs:s.Nonempty) : price s≤δ := pay a b x hx s hs
  have combine : ‖reading R d o (Y a b o) (U a b o) live full-q‖ ≤
      price {0,1}+‖m 1‖*price {0}+‖m 0‖*price {1} :=
    WilsonAddressedWeakCompensatedHearing.original R gr live d o (Y a b o) (U a b o) m q hj
      (house p k gr live d hd ρ hr small x hx _ _)
  refine combine.trans ?_
  calc
    _ ≤ δ+C*δ+C*δ := add_le_add (add_le_add (priced {0,1} (by simp))
      (mul_le_mul (bounded 1) (priced {0} (by simp)) (by dsimp [price,fee];positivity) hC.le))
      (mul_le_mul (bounded 0) (priced {1} (by simp)) (by dsimp [price,fee];positivity) hC.le)
    _ = η := by dsimp [δ];field_simp [show 1+2*C≠0 by positivity];ring

end YM.Integration.WilsonAddressedWeakRankHearing
