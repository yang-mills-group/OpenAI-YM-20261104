import YM.Integration.WilsonAddressedWeakCompensatedHearing
import YM.Integration.WilsonAddressedWeakCalibration

/-! A fixed physical support pays both proper detector coefficients and fits the original reflection chamber. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakShapeFees
open Filter Function Set MeasureTheory Metric Lattice Wilson RG Source Cells RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox PhysicalNext.Repeat.Legato
open MergeProof Accent Motion Bandage Extra.Multi Menu
open FVA2 FVA2.ColorCode Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone
open Extraction Table Spec OPE OPE.Orbits PhysMS XSpace XSpace.Normalize Trace Trace.Pilot
open WilsonThermometerOffsetTrajectory WilsonAddressedWeakPointCells
open scoped Classical BigOperators Topology

variable {G:Gauge} {B:Local.Physical.Deck G} {O:Booked B} (M:MS_Data G O)
variable {D:ℕ}

/-- The independent one-field reading at its own actual child. -/
def mean (a:Glyph B D) (x:Points 2) (i:Fin 2) (μ:ℝ) : ℂ :=
  Dial.tour M (fun _:Fin 1=>labelAt B a) μ (fun _:Fin 1=>Fountain.metric x i) Finset.univ 0

theorem proper (φ:Test 2) (μ:ℝ) :
    ∃ C:ℝ,0<C ∧ ∀ x∈cthickening 1 (tsupport φ),∀ (a:Glyph B D) (i:Fin 2),‖mean M a x i μ‖≤C := by
  let A (x:Points 2) (v:Glyph B D × Fin 2) := mean M v.1 x v.2 μ
  have hm : Continuous (Fountain.metric (m:=2)) := by
    apply continuous_pi
    intro i
    exact Theater.out.toLinearMap.continuous_of_finiteDimensional.comp
      ((continuous_apply i).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin 2=>E4)).continuous)
  have con : Continuous A := by
    apply continuous_pi; intro v
    apply continuous_iff_continuousAt.mpr
    intro x
    let X := fun z:Points 2=>fun _:Fin 1=>Fountain.metric z v.2
    have hx : Continuous X := continuous_pi fun _=>(continuous_apply v.2).comp hm
    exact ((Dial.contin M (fun _:Fin 1=>labelAt B v.1) (X x)
      (Function.injective_of_subsingleton _) Finset.univ 0 μ).1.comp hx.continuousAt)
  have K : IsCompact (cthickening 1 (tsupport φ)) := φ.hasCompactSupport.cthickening
  obtain ⟨b,hb⟩ := (K.image con).isBounded.exists_norm_le
  refine ⟨max 1 b,lt_max_of_lt_left zero_lt_one,?_⟩
  intro x hx a i
  exact (norm_le_pi_norm (A x) (a,i)).trans ((hb _ ⟨x,hx,rfl⟩).trans (le_max_right ..))

theorem chamber (R:Run G) (D χ:ℕ) (φ:Test 2) :
    ∃ ρ₀:ℝ,0<ρ₀ ∧ ∀ᶠ N:ℕ in atTop, ∀ p k (gr:χ≤k) (live:k≤N) (d:Fin 2→ℕ) (_:∀ i,d i≤D)
      (ρ:ℝ) (_:0<ρ) (_:ρ≤ρ₀) (x:Points 2),φ x≠0 →
      let z:=WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
      ∀ (y:(i:Fin 2)→Palette R.family (d i)) (r:(i:Fin 2)→Emblems R.family (d i)) i,
      Interior ((Cells.center R.family.S p (gr.trans live) 0).chamber 0)
        (WilsonThermometerIntrinsicRoster.source R d z y r live i) := by
  obtain ⟨b,hb⟩ := φ.hasCompactSupport.isBounded.exists_norm_le
  let A:=max 1 b
  have pos : 0<A := lt_max_of_lt_left zero_lt_one
  have mesh := R.family.S.a_pos χ
  refine ⟨R.family.S.a χ/(8*A),by positivity,?_⟩
  filter_upwards [WilsonAddressedWeakChamber.original R χ D,
    (tendsto_order.mp R.family.S.shrinks).2 (R.family.S.a χ/8) (by positivity)] with N roof fine
  intro p k g live d hd ρ hr fit x hx
  apply roof p (g.trans live) k live d hd ρ hr x
  intro i
  have hb' : ‖x i‖ ≤ A := (PiLp.norm_apply_le x i).trans
    ((hb x (subset_tsupport _ (mem_support.mpr hx))).trans (le_max_right ..))
  have pay := (le_div_iff₀ (show 0<8*A by positivity)).mp fit
  have lo := mul_le_mul_of_nonneg_left hb' hr.le
  nlinarith only [pay,lo,fine.le]

end YM.Integration.WilsonAddressedWeakShapeFees
