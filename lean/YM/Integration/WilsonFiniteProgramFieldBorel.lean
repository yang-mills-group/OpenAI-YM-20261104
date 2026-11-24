import YM.Comparison.RG02.Bulk.Fk
import YM.Comparison.RG02.Order.Eval
import Mathlib.MeasureTheory.Integral.Prod

/-! The original finite Wick program can be read on any measurable held field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFiniteProgramFieldBorel
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open Comparison.RG02.Cumulants Cumulants.Cloud
open Extra.Trajectories Primitives.GCC.Anchor
open scoped Topology BigOperators Classical ContDiff

variable {X : Type*} [MeasurableSpace X] {V : Type} [Fintype V] [DecidableEq V] {R : Census V}

private def Borel (f : X → Poly R) := ∀ s, Measurable (fun x => (f x).part s)

omit [Fintype V] in
private lemma product {f h : X → Poly R} (hf : Borel f) (hh : Borel h) :
    Borel (fun x => f x * h x) := by
  intro s
  simp only [Poly.part_mul]
  apply Finset.measurable_fun_sum
  intro i _
  apply Finset.measurable_fun_sum
  intro j _
  split_ifs <;> first | exact (hf i).mul (hh j) | exact measurable_const

omit [Fintype V] in
private lemma power {f : X → Poly R} (hf : Borel f) (k : ℕ) : Borel (fun x => f x ^ k) := by
  induction k with
  | zero => exact fun _ => by simpa only [pow_zero] using (measurable_const : Measurable (fun _ : X => (1 : Poly R).part _))
  | succ k ih => simpa only [pow_succ] using product ih hf

private lemma exponential {f : X → Poly R} (hf : Borel f) : Borel (fun x => (f x).pass) := by
  intro s
  simp only [Poly.pass, Poly.part_sum, Poly.part_smul]
  exact Finset.measurable_fun_sum _ (fun k _ => measurable_const.mul (power hf k s))

private lemma logarithm {f : X → Poly R} (hf : Borel f) : Borel (fun x => connected (f x)) := by
  unfold connected
  generalize Fintype.card V = n
  induction n with
  | zero => exact fun _ => measurable_const
  | succ n ih =>
    intro s
    simp only [iteration, Poly.part_plus, part_sub]
    exact (ih s).add ((hf s).sub (exponential ih s))

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G}
    {O : ChartRatio G} (K : Bulk.Kernel S p P O) (F : Forest S.ratio)
    (tag : S.Choices) (W : Bulk.Colors R G f)

private lemma primitive (n : ℕ) (v : Multi.Hot (Order.Board R n)) :
    Continuous (fun az : fieldDir G c 1 × (Precision.Key F G → ℝ) =>
      paint az.2 (Assembly.generator (Bulk.stage K F az.1) (Bulk.hinge F) W.power
        (Bulk.markFn S F W) (Bulk.geometric K F tag W) n v)) := by
  simp only [Assembly.generator, map_smul]
  split_ifs with h
  · simp only [Assembly.reading, Assembly.jet, Assembly.translate, Bulk.stage, Bulk.classical_point]
    fun_prop
  · simp only [Assembly.readingVacuum, Assembly.vacuumLetter]
    split_ifs
    · exact continuous_const
    · simp only [Assembly.jet, Assembly.translate, Bulk.stage, Bulk.classical_point]
      fun_prop

omit [Fintype V] in
private lemma gaussian_parameter {I : Type} [Fintype I] [DecidableEq I]
    (Q : Matrix I I ℝ) (hQ : Q.IsSymm) (hp : Q.PosSemidef)
    (h : X → Multi.Hot R → Next.Rank.Normal.poly I)
    (hv : ∀ v, Measurable (fun az : X × (I → ℝ) => paint az.2 (h az.1 v))) :
    Borel (fun a => Cloud.prescription Q hQ 0 (h a)) := by
  intro s
  have hm : Measurable (fun az : X × (I → ℝ) => paint az.2 (integrand (h az.1) s)) := by
    simp only [integrand, _root_.map_sum, _root_.map_prod]
    exact Finset.measurable_fun_sum _ fun _ _ => Finset.measurable_fun_prod _ fun v _ => hv v
  have eqn (a : X) :
      (∫ z : I → ℝ, paint z (integrand (h a) s) ∂Gaussian.cloud Q) =
        (Cloud.prescription Q hQ 0 (h a)).part s := by
    have hw := (paid Q hQ hp (0 : I → ℝ) (integrand (h a) s)).2
    rw [shift_zero] at hw
    simpa only [Cloud.prescription, Poly.inject, Poly.part, zero_add] using hw
  simp_rw [← eqn]
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

private lemma moment (n : ℕ) : Borel (fun A => Bulk.Fk K F tag W A n) := by
  unfold Bulk.Fk Assembly.prescription
  exact gaussian_parameter _ _ (K.positive F tag).posSemidef _ (fun v => (primitive K F tag W n v).measurable)

private lemma quotiented (n : ℕ) :
    Borel (fun A => Order.ratio (Bulk.Fk K F tag W A n)) := by
  have hm := moment K F tag W n
  have hb : Borel (fun A => Order.denominator (Bulk.Fk K F tag W A n)) := by
    intro s
    rw [← Order.Join.pair_reunite s]
    simp only [Order.denominator, Order.bottom_value]
    split_ifs
    · exact hm _
    · exact measurable_const
  apply product hm
  apply exponential
  intro s
  exact (logarithm hb s).neg

private lemma evaluated {n : ℕ} {h : X → Order.Grade R n} (hh : Borel h) (g : ℂ) :
    Borel (fun x => Order.value g (h x)) := by
  intro s
  simp only [Order.value, Poly.part_sum, Poly.part_smul]
  apply Finset.measurable_fun_sum
  intro k _
  apply measurable_const.mul
  simp only [Order.observe]
  split_ifs
  · exact measurable_const.mul (hh _)
  · exact measurable_const

/-- Every ordinary face of the original normalized finite program is Borel in its entire
held field. The same covariance and denominator enter every face. -/
theorem original (g : ℝ) (n : ℕ) (s : R.Mode) :
    Measurable (fun A => (Order.value (g : ℂ) (Order.ratio (Bulk.Fk K F tag W A n))).part s) :=
  evaluated (quotiented K F tag W n) g s

theorem connected_read (g : ℝ) (n : ℕ) (s : R.Mode) :
    Measurable (fun A => (Order.value (g : ℂ) (Order.logMarked (Bulk.Fk K F tag W A n))).part s) :=
  evaluated (logarithm (quotiented K F tag W n)) g s

end YM.Integration.WilsonFiniteProgramFieldBorel
