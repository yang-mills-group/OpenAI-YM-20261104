import YM.Integration.FVA1Physical.Round2.PurchasedFieldExterior
import YM.Integration.FVA1Physical.Round2.FieldLocalWilson
import YM.Integration.FVA1Physical.Sources.Round2.PurchasedFieldTaylor

/-! Actual mixed field insertions have a single sup bound before placements
and include both endpoints of every oriented link read by their stencils. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior
open RGComparison.Core16 RGComparison.Core16.Spool
open MSbar MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Mosaic MSbar.Bulk
open MSbar.Bakery MSbar.Whisk Push.Uniform YM.Integration.FVA1Physical.Wilson
open scoped Classical Topology
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι → Lamp G)

def stencilBound := 1+(encouraging J).choose

theorem stencilBound_pos : 0 < stencilBound J :=
  add_pos_of_pos_of_nonneg zero_lt_one (encouraging J).choose_spec.1

theorem stencil_bounded {f : Side} (o : ι → Site f) (part : Bool) (U : Config G f) :
    |look part (tally J o U)| ≤ stencilBound J := by
  rw [←exhibition J o U,←Real.norm_eq_abs]
  exact ((encouraging J).choose_spec.2 part _).trans (le_add_of_nonneg_left zero_le_one)

theorem collar_stencil_local {c f : Side} (S : StepData c f) (F : Forest S.ratio)
    (o : ι → Site f) (part : Bool) (b : Site f) (y : ℝ)
    (inside : ∀ i : Slice J, separation b (legs J o i).1 ≤ spotN y) :
    GaugeLocal S (youth F (boxY y b)) (fun U => look part (tally J o U)) := by
  refine ⟨⟨((look part).continuous.comp (tally_cont J o)).measurable,stencilBound J,
    stencil_bounded J o part⟩,fun k _ U => congrArg (look part) (tally_invariant J o k U),?_⟩
  intro U W same
  change look part (tally J o U) = look part (tally J o W)
  rw [←exhibition J o U,←exhibition J o W]
  apply congrArg (fun v => look part (exhibit J v))
  funext i
  have hx : (legs J o i).1 ∈ boxX y b := (halo_spec ..).mpr ⟨b,mem_singleton_self _,inside i⟩
  have hy : (legs J o i).1 ∈ boxY y b := halo_subset _ _ hx
  have ep : (legs J o i).1+step (legs J o i).2 ∈ boxY y b := by
    apply (halo_spec ..).mpr
    exact ⟨_,hx,(Work.E01.sep_step_le _ _).trans (by omega)⟩
  exact same _ (halo_subset _ _ hy) (halo_subset _ _ ep)

theorem finite_taste_transfer (p : ℕ) (a b : PowerSeries ℝ) {t E : ℝ}
    (ht : 0 ≤ t) (h1 : t ≤ 1) (rows : ∀ i ≤ p, |PowerSeries.coeff i a-PowerSeries.coeff i b| ≤ E) :
    |taste p a t - taste p b t| ≤ (p+1:ℕ)*E := by
  unfold taste
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  calc (∑ i ∈ range (p+1), |t^i * PowerSeries.coeff i a - t^i * PowerSeries.coeff i b|) ≤
           ∑ _i ∈ range (p+1), E := by
             apply sum_le_sum
             intro i hi
             rw [←mul_sub,abs_mul,abs_of_nonneg (pow_nonneg ht _)]
             exact (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ ht h1)).trans
               (rows i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
       _ = _ := by rw [sum_const,card_range,nsmul_eq_mul]

end YM.Integration.FVA1Physical.Round2.Curvature
