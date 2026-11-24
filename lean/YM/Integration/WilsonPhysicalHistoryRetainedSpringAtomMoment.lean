import YM.Integration.WilsonPhysicalHistoryRetainedSpringPooling
import YM.Integration.WilsonPhysicalHistoryRetainedSpringIntegral

/-! Every moment of a curvature Taylor error uses only the higher moments
of the ordered bonds in that same angular sample. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open MeasureTheory Finset RG Wilson Precision Lattice WilsonMeasuredPathTaylor
open FundedCurvatureRayTaylor WilsonSlotContactTruncation
open scoped Classical BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {Ω : Type*} [MeasurableSpace Ω] {G : Gauge} {k : ℕ} {n : Side}

private theorem visit_sum {ι : Type*} {μ : Measure Ω} {f : ι→Ω→ℝ} (s : List ι)
    (h : ∀ i∈s,AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun z=>(s.map fun i=>f i z).sum) μ := by
  induction s with
  | nil => exact aestronglyMeasurable_const
  | cons i s ih =>
    exact (h i List.mem_cons_self).add (ih (fun j hj=>h j (List.mem_cons_of_mem _ hj)))

theorem atom_moment (μ : Measure Ω) (v : Ω→Directions G n) (a : Atom G k) (x : Site n)
    (q l : ℕ) (t : ℝ) {M σ : ℝ} (pos : 0<M) (hs : 0<σ)
    (meas : ∀ b,∀ e∈contacts x (letters a b),AEStronglyMeasurable (fun z=>speed (v z) e) μ)
    (hot : ∀ b,∀ e∈contacts x (letters a b),Integrable (fun z=>speed (v z) e^((q+1)*(l+1))) μ ∧
      (∫ z,speed (v z) e^((q+1)*(l+1)) ∂μ)≤M^((q+1)*(l+1)))
    (printed : AEStronglyMeasurable (fun z=>(a.unmasked (field (v z) t) x:ℂ)-polynomial a x (v z) q t) μ) :
    let E:=fun z=>(a.unmasked (field (v z) t) x:ℂ)-polynomial a x (v z) q t
    Integrable (fun z=>‖E z‖^(l+1)) μ ∧
      (∫ z,‖E z‖^(l+1) ∂μ)≤(a.budget σ*(2*M*|t| /σ)^(q+1))^(l+1) := by
  intro E
  let c (b : Fin k→G.ColorIndex):=|a.coeff b| * (|t|^(q+1)/(q+1).factorial)
  let s (b : Fin k→G.ColorIndex) (z : Ω):=score (v z) x (letters a b)
  let u b z:=c b*(s b z)^(q+1)
  let π b:=c b*(2*(a.length:ℝ)*M)^(q+1)
  have c0 b : 0≤c b:=by dsimp only [c]; positivity
  have s0 b z : 0 ≤ s b z:=by
    change 0≤((contacts x (letters a b)).map (speed (v z))).sum
    apply List.sum_nonneg
    intro d hd
    obtain ⟨e,-,rfl⟩:=List.mem_map.mp hd
    exact norm_nonneg (G.colorMat (v z e))
  have sm b : AEStronglyMeasurable (s b) μ:=visit_sum _ (meas b)
  have eu b : AEStronglyMeasurable (u b) μ:=((continuous_pow (q+1)).comp_aestronglyMeasurable
    (sm b)).const_mul (c b)
  have power : 0<(q+1)*(l+1):=Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have index : (q+1)*(l+1)-1+1=(q+1)*(l+1):=by omega
  have income b : Integrable (fun z=>(s b z)^((q+1)*(l+1))) μ ∧
      (∫ z,(s b z)^((q+1)*(l+1)) ∂μ)≤(2*(a.length:ℝ)*M)^((q+1)*(l+1)) := by
    simpa only [index] using score_moment μ v ((q+1)*(l+1)-1) pos a x b (meas b)
      (fun e he=>by simpa only [index] using hot b e he)
  have pay b : Integrable (fun z=>(u b z)^(l+1)) μ ∧
      (∫ z,(u b z)^(l+1) ∂μ)≤(π b)^(l+1) := by
    have scaled z : (u b z)^(l+1)=(c b)^(l+1)*(s b z)^((q+1)*(l+1)):=by
      dsimp only [u]
      rw [mul_pow,←pow_mul]
    have tariff : (π b)^(l+1)=(c b)^(l+1)*(2*(a.length:ℝ)*M)^((q+1)*(l+1)):=by
      dsimp only [π]
      rw [mul_pow,←pow_mul]
    simp only [scaled,tariff,integral_const_mul]
    exact ⟨(income b).1.const_mul _,mul_le_mul_of_nonneg_left (income b).2 (pow_nonneg (c0 _) _)⟩
  have whole:=pool_finite μ univ π u (fun b _=>by dsimp only [π]; positivity [c0 b])
    (fun b _ z=>mul_nonneg (c0 b) (pow_nonneg (s0 b z) _)) (fun b _=>eu b) l (fun b _=>pay b)
  have point z : ‖E z‖^(l+1)≤(∑ b,u b z)^(l+1):=by
    apply pow_le_pow_left₀ (norm_nonneg _)
    apply (atom_path_error a x (v z) q t).trans_eq
    exact Finset.sum_congr rfl fun b _=>by dsimp only [c,s,u]; ring
  have hi:=whole.1.mono' ((continuous_pow (l+1)).comp_aestronglyMeasurable printed.norm)
    (ae_of_all _ fun z=>by rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]; exact point z)
  refine ⟨hi,(integral_mono hi whole.1 point).trans (whole.2.trans ?_)⟩
  apply pow_le_pow_left₀ (Finset.sum_nonneg fun b _=>by dsimp only [π]; positivity [c0 b])
  apply le_trans _ (length_taylor a hs pos.le q t)
  unfold Atom.magnitude
  rw [Finset.sum_mul]
  exact le_of_eq (Finset.sum_congr rfl fun b _=>by dsimp only [π,c]; ring)

end YM.Integration.OriginalMarkedRunAction
