import YM.WilsonMS.Beta.ShellKinetic
import YM.FormalOPE.RG10.MultiGauge.Degree
/-!
# Polynomial operators for the remaining Gaussian integrals
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BetaValue
open Function Filter Set Finset MeasureTheory Metric
open LoopRank Lattice MS Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect
  Native
open Book Convolve City Logarithm Signal Landau.Detect.Mark Wind High Knobs
open LogTime LogTime.IntervalFamily Outlook Land Arc Wire Rock Path Oceans Plum Alps Garment Color
  Pearl
open Arts Motif Halo
open _root_.YM.PertExtension
open RG FormalOPE FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open Complex (I)
open scoped Topology ContDiff BigOperators
variable (p q : QP) (a b : Axis) (t r : ℝ)
namespace HeatPapers

abbrev poly :=
  papers QP

abbrev Poly :=
  Permit QP

abbrev lambda (i : Axis) : QP →ₗ[ℝ] ℝ :=
  LinearMap.proj i

def Beam (α : ℝ) (h : 0 < α) : GaussianScore.Law QP
    where
  P :=
    LinearMap.mk₂ ℝ (fun x y : QP => 2 * α * (∑ i : Axis, x i * y i))
      (fun x y z => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add])
      (fun c x y => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
        ring)
      (fun x y z => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
      (fun c x y => by
        simp_rw [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← Finset.mul_sum]
        ring)
  turns x
    y := by
    simp only [LinearMap.mk₂_apply]
    simp_rw [mul_comm (x _) (y _)]
  slope :=
    ⟨α, h, fun x => by
      obtain ht := sup_square x
      rw [LinearMap.mk₂_apply, show ∑ i : Axis, x i * x i = x.sq from ?_]
      swap
      · simp only [Momentum.sq, pow_two]
      nlinarith [mul_le_mul_of_nonneg_left ht h.le]⟩
  smooth := by
    simp only [LinearMap.mk₂_apply]
    fun_prop

lemma kernel_val (α : ℝ) (h : 0 < α) (p : QP) : (Beam α h).kern p = exp (-α * p.sq) := by
  unfold GaussianScore.Law.kern Beam
  simp only [LinearMap.mk₂_apply, Momentum.sq, pow_two]
  ring_nf

abbrev spring (x : ℝ) : Poly :=
  algebraMap ℝ _ x

def petal (i : Axis) : Poly :=
  ⟨lambda i, Papers.linear _⟩

def meterR (q : QP) : Poly →ₐ[ℝ] ℝ :=
  (Pi.evalAlgHom ℝ _ q).comp poly.val

lemma atP : meterR q (petal a) = q a :=
  rfl

lemma atR : meterR q (spring t) = t :=
  rfl

abbrev Sheet (f : QP → ℝ) : Prop :=
  f ∈ poly

lemma Pα (f : QP → ℝ) (h : Sheet f) (α : ℝ) (hα : 0 < α) :
    Integrable (fun p : QP => exp (-α * p.sq) * f p) (covMeasure Axis) := by
  let U := Beam α hα
  rw [show (fun p : QP => exp (-α * p.sq) * f p) = f * U.kern from ?_]
  exact Papers.useful (covMeasure Axis) (Beam α hα) ⟨f, h⟩
  ext p
  rw [Pi.mul_apply, kernel_val]
  ring

lemma Temp (f : QP → ℝ) (h : Sheet f) : Continuous f :=
  (Papers.applies (show Poly from ⟨f, h⟩)).1
namespace Sheet
variable {f g : QP → ℝ}

lemma read (p : Axis) : Sheet (fun x : QP => x p) :=
  (petal p).property

lemma num (r : ℝ) : Sheet (fun _ => r) :=
  (spring r).property

lemma add (h : Sheet f) (ht : Sheet g) : Sheet (fun i => f i + g i) :=
  poly.add_mem h ht

lemma sub (h : Sheet f) (ht : Sheet g) : Sheet (fun i => f i - g i) :=
  poly.sub_mem h ht

lemma neg (h : Sheet f) : Sheet (fun i => -f i) :=
  poly.neg_mem h

lemma mul (h : Sheet f) (ht : Sheet g) : Sheet (fun i => f i * g i) :=
  poly.mul_mem h ht

lemma pow (h : Sheet f) (u : ℕ) : Sheet (fun i => f i ^ u) := by
  induction u with
  | zero =>
    simp_rw [pow_zero]
    exact num _
  | succ u ih =>
    simp_rw [pow_succ]
    exact ih.mul h

lemma sums {J : Type} (I : Finset J) (V : J → QP → ℝ) (h : ∀ i ∈ I, Sheet (V i)) :
    Sheet (fun v => ∑ i ∈ I, V i v) := by
  rw [show (fun v => ∑ i ∈ I, V i v) = ∑ i ∈ I, V i from funext fun v => (Finset.sum_apply ..).symm]
  exact poly.sum_mem h

lemma vers (h : Sheet f) (u : ℝ) (p : QP) : Sheet (fun i => f (u • i + p)) :=
  Papers.consign (u • LinearMap.id (R := ℝ)) _ h

lemma wave (h : Sheet f) (p : QP) : Sheet (fun i => f (i + p)) := by
  simpa only [one_smul] using vers h 1 p

lemma heat_sq : Sheet Momentum.sq := by
  unfold Momentum.sq
  exact sums _ _ fun i _ => (read i).pow _

lemma face (a b : Axis) : Sheet (precision a b) := by
  unfold precision Landau.delta
  split
  exact heat_sq.sub ((read a).mul (read b))
  exact (num 0).sub ((read a).mul (read b))

lemma Ptri {f g u : QP → QP} (h : ∀ i, Sheet (fun x => f x i)) (ht : ∀ i, Sheet (fun x => g x i))
    (hx : ∀ i, Sheet (fun x => u x i)) (a b c : Axis) :
    Sheet (fun x => trident (f x) (g x) (u x) a b c) := by
  have hv (f : QP → QP) (h : ∀ i, Sheet (fun x => f x i)) (a b c : Axis) :
    Sheet (fun i => polar0 (n := 0) a b c (f i)) := by
    have he (a b x : Axis) : Sheet (fun i => Landau.delta a b (f i x)) := by
      unfold Landau.delta
      split
      exact h _
      exact num 0
    exact (he b c a).sub (he a c b)
  exact Sheet.add (Sheet.add (hv f h _ _ _) (hv g ht _ _ _)) (hv u hx _ _ _)

lemma triP (b c : Axis) : Sheet (fun q : QP => Vtri p q b c) := by
  unfold Vtri
  exact Ptri (fun i => by exact ((read i).add (num _)).neg) read (fun i => num (p i)) _ _ _

lemma turtle : Sheet (Musc p) := by
  have hx : ∀ a b : Axis, Sheet (fun q => Bones p q a b) := fun a b =>
    sums _ _ fun i _ => sums _ _ fun j _ => (((face i j |>.wave p).mul (triP p _ _)).mul (triP p _ _))
  unfold Musc
  apply
    sub (f := fun q => 2 * (_ : ℝ))
      ((num _).mul (sums _ _ (fun a _ => sums _ _ fun b _ => (face a b).mul (hx _ _))))
      (mul ((num _).mul (heat_sq.mul (read _))) ((heat_sq.wave p).mul ((read 1).wave p)))

lemma flame : Sheet (fun q : QP => 2 * t * (q.sq + (q + Kproj t).sq) * precision 0 0 q) :=
  (((num _).mul ((heat_sq).add (heat_sq.wave _))).mul (face 0 0))
end Sheet
end HeatPapers
end YM.WilsonMS.BetaValue
