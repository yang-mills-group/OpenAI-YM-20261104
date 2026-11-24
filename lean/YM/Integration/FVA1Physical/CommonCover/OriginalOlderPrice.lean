import YM.Comparison.RG02.Integral.Comparison
import YM.Comparison.RG02.Integral.Healthy
import YM.SectorNext.VACUUM_NORMALIZATION.Stripped
import YM.Integration.FVA1Physical.CommonCover.OlderMixedPrice

/-! The inherited term of the actual tagged Haar push, centered at the
same prescribed coefficient as the normalized Wilson numerator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.OlderPrice
open MeasureTheory Filter RG Wilson Gauge Precision Tree Lattice Exterior
open Comparison.RG02 Order Marker Multi Integral Actual Push.SectorMeasure
open scoped Classical

variable {I : Type} [DecidableEq I] [Fintype I] {R : Census I}

omit [Fintype I] in
private theorem part_sub (P Q : Poly R) (s : R.Mode) :
    (P-Q).part s=P.part s-Q.part s := by
  rw [sub_eq_add_neg,Poly.part_plus,Poly.part_neg,sub_eq_add_neg]

omit [Fintype I] in
theorem tagged_center (D M : Poly R) (s : R.Mode) (q : ℂ) {a b k : ℝ}
    (ha : 0<a) (hb : 0<b) (hk : 0≤k)
    (da : D.part R.quiet=(a:ℂ)) (mb : M.part R.quiet=(b:ℂ)) :
    ‖((k:ℂ) • (D-M)).part s - ((k:ℂ) • (D-M)).part R.quiet*q‖ ≤
      k*(a*‖(unitScale D).part s-(unitScale M).part s‖+
        max a b * |Real.log a-Real.log b| * ‖(unitScale M).part s-q‖) := by
  have positive (v : ℝ) (hv : 0<v) (P : Poly R) (h : P.part R.quiet=(v:ℂ)) :
      (v:ℂ)*(unitScale P).part s=P.part s := by
    rw [unitScale,Poly.part_smul,h,mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr hv.ne')]
  have eq : ((k:ℂ) • (D-M)).part s - ((k:ℂ) • (D-M)).part R.quiet*q =
      (k:ℂ)*((a:ℂ)*(unitScale D).part s-(b:ℂ)*(unitScale M).part s-((a-b:ℝ):ℂ)*q) := by
    rw [positive a ha D da,positive b hb M mb,Poly.part_smul,Poly.part_smul,
      part_sub,part_sub,da,mb,Complex.ofReal_sub]
    ring
  rw [eq,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hk]
  exact mul_le_mul_of_nonneg_left (centered_coefficient ha hb _ _ q) hk

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
    (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices)
    (g c₀ : ℝ) (x : fieldDir G c 1) (W : Bulk.Colors R G f)

def olderPrice (vac : Config G f → ℝ) (D : Lit R (Config G f)) (s : R.Mode) (q : ℂ)
    (y : F.Slice G) : ℝ :=
  let U := F.drape y
  let v := (unitScale (model g c₀ W K U)).part s
  let b := weight g c₀ U W p P
  taggedKernel S (temperature g) t U (sample g x) *
    (vac U * ‖(unitScale (D U)).part s-v‖ +
      max (vac U) b * |Real.log (vac U)-Real.log b| * ‖v-q‖)

/-- Restrict the original Haar slice before integrating. The two prices
are for the normalized incoming field mismatch and the vacuum log change
times the centered model reading. No Taylor series for the actual error
is needed. -/
theorem centered_older (A : Set (F.Slice G)) (hA : MeasurableSet A)
    (vac : Config G f → ℝ) (D : Lit R (Config G f)) (s : R.Mode) (q : ℂ)
    (quiet : ∀ U, (D U).part R.quiet=(vac U:ℂ)) (pos : ∀ y∈A, 0<vac (F.drape y))
    (well : Bulk.Well W) (leaf : Leaf.All D)
    (finite : IntegrableOn (olderPrice K F t g c₀ x W vac D s q) A (F.order G)) :
    let E := charge (F.order G) (older K F t g c₀ x W A D)
    ‖E.part s-E.part R.quiet*q‖ ≤ ∫ y in A, olderPrice K F t g c₀ x W vac D s q y ∂F.order G := by
  intro E
  let raw := stack t (sample g x) (temperature g) (olderInput K g c₀ W D) ∘ F.drape
  have good : Good ((F.order G).restrict A) raw := (good_slice F t (sample g x) (temperature g) K.branches
    (leaf_sub leaf (leaf_model K g c₀ W well))).within A
  change ‖(charge (F.order G) (A.indicator raw)).part s -
    (charge (F.order G) (A.indicator raw)).part R.quiet*q‖ ≤ _
  rw [←restricted_cost hA raw,components,components,←integral_mul_const,
    ←integral_sub (good s) ((good R.quiet).mul_const q)]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg (Eventually.of_forall fun _=>norm_nonneg _) finite
  filter_upwards [ae_restrict_mem hA] with y hy
  change ‖((_:ℂ) • (D (F.drape y)-model g c₀ W K (F.drape y))).part s -
    ((_:ℂ) • (D (F.drape y)-model g c₀ W K (F.drape y))).part R.quiet*q‖ ≤ _
  exact tagged_center (D (F.drape y)) (model g c₀ W K (F.drape y)) s q
    (pos y hy) (Real.exp_pos _) (kernel_nonneg _ _ _ _) (quiet _) (model_unit ..)

end YM.Integration.FVA1Physical.OlderPrice
