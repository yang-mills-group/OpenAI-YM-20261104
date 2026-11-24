import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Courants
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Narrow

/-! The physical residual square retained by the short classical exponent.
The full center solves the normal equation for the same affine rows. The
difference is priced at each scalar row before summing over translations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarRows
open Filter Function Lattice RG Wilson Pressure Pressure.Stores Tree Precision
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Control
open ConnectedActivityE6.Window ConnectedActivityE6.Pulse ConnectedActivityE6.Blaze
open Brush Foramen Vine Tablet ConnectedActivityE6.Census Itinerary Matrix Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f}
  {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {j m : ℕ} {η r Q γ v z w d b : ℝ} {x : E}

/-- Unwindowed normal-equation solution in the actual completed coordinates. -/
def fullCenter (X : Coat T F) := -((X.plate⁻¹).transpose *ᵥ X.linearBill)

theorem normal (X : Coat T F) (h : Allow X.plate (along S) m η r Q) :
    X.plate *ᵥ fullCenter X + X.linearBill = 0 := by
  have hs : (X.plate⁻¹).transpose = X.plate⁻¹ := by
    ext i k
    simpa only [IsHermitian,conjTranspose_apply,transpose_apply,star_trivial] using
      X.balanced.inv.apply i k
  rw [fullCenter,hs,Matrix.mulVec_neg,mulVec_mulVec,h.initial.1,one_mulVec,neg_add_cancel]

def residual (X : Coat T F) (a : Tubular f G → ℝ) :=
  stand (X.priced 0) + X.form *ᵥ a

def displacement (X : Coat T F) :=
  - (X.form *ᵥ ((X.kernelA - X.plate⁻¹).transpose *ᵥ X.linearBill))

theorem split (X : Coat T F) :
    residual X X.driftM = residual X (fullCenter X) + displacement X := by
  unfold residual fullCenter displacement Coat.driftM
  rw [Matrix.transpose_sub, Matrix.sub_mulVec,Matrix.mulVec_sub]
  simp only [Matrix.mulVec_neg]
  abel

/-- The orientation average and the even and odd parent rows in the original
stored label. No per-lattice scalar normalization is inserted. -/
theorem retained (X : Coat T F) (h : P.Funds S T) (s : Signed) (p : Spot c f) :
    Raw.orientation * X.extracted X.μ s p =
      ∑ a ∈ parents p, ∑ k : G.ColorIndex, (residual X X.driftM ((s,a),k))^2/2 := by
  obtain ⟨_,_,hf,_⟩ := h.feeds
  have he : residual X X.driftM = stand (X.priced X.μ) := (X.pricing hf X.μ).symm
  rw [he,Coat.extracted,Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_div]
  have ht : (∑ k : G.ColorIndex, (stand (X.priced X.μ) ((s,a),k))^2) =
      ‖X.priced X.μ (s,a)‖^2 := by rw [EuclideanSpace.real_norm_sq_eq]; rfl
  rw [ht]
  unfold Coat.surcharge Coat.priced
  by_cases hs : X.selected s (spot S a)
  · simp only [hs,if_true,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,
      Coat.scale,Real.sq_sqrt (by positivity : 0 ≤ (Fintype.card Signed:ℝ)⁻¹)]
    unfold Raw.orientation
    ring
  simp [hs]

/-- Exact rooted disagreement. The linear cross term survives at an
individual row, even when a sum over rows satisfies a normal equation. -/
theorem square_difference (X : Coat T F) (i : Coat.Target c f G) :
    (residual X X.driftM i)^2/2 - (residual X (fullCenter X) i)^2/2 =
      displacement X i * residual X (fullCenter X) i + (displacement X i)^2/2 := by
  rw [split]
  rw [Pi.add_apply]
  ring

theorem stored_square (X : Coat T F) (h : P.Funds S T) (s : Signed) (p : Spot c f) :
    Raw.orientation * X.extracted X.μ s p -
      (∑ a ∈ parents p, ∑ k : G.ColorIndex, (residual X (fullCenter X) ((s,a),k))^2/2) =
      ∑ a ∈ parents p, ∑ k : G.ColorIndex,
        (displacement X ((s,a),k) * residual X (fullCenter X) ((s,a),k) +
        (displacement X ((s,a),k))^2/2) := by
  rw [retained X h,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [←Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => square_difference X ((s,a),k)

def normalizedPrice (j : ℕ) (v z : ℝ) := v*(1+z)^j

/-- The cost is independent of the number of fine bonds. The scalar uses
only one rooted affine row, a window-inverse discrepancy, full inverse,
and the original affine offset and linear map. -/
theorem square_jets (X : Coat T F) (U : E → Config G c) (i : Coat.Target c f G)
    (h : Allow (vary X (U x)).plate (along S) m η r Q)
    (hγ : γ ≤ retain η r Q)
    (hA : Tablet j γ v z (fun y => (vary X (U y)).plate) (along S) (along S) x)
    (hD : Tablet j γ w d (fun y => (vary X (U y)).form) (aim S) (along S) x)
    (hb : 0 ≤ b) (h₀ : ∀ k, Brush j b 1 (fun y => stand ((vary X (U y)).priced 0) k) x) :
    let n := payE η r Q m
    let K := token j v n
    let Z := driftP j z
    let E₀ := K * tidal γ v (facePrice j X.B m v n) X.B
    let J := normalizedPrice j (w*b) (d+1)
    let C := normalizedPrice j (K*J) (Z+1)
    let Cₑ := normalizedPrice j (E₀*J) ((Z+(z+Z))+1)
    let f := b + normalizedPrice j (w*C) (d+1)
    let e := normalizedPrice j (w*Cₑ) (d+1)
    Brush j (e*f+e*e/2) 2 (fun y => let Y := vary X (U y)
      (residual Y Y.driftM i)^2/2 - (residual Y (fullCenter Y) i)^2/2) x := by
  intro n K Z E₀ J C Cₑ f e
  let Y y := vary X (U y)
  have hJ (k : Tubular _ G) : Brush j J 1 (fun y => (Y y).linearBill k) x :=
    (beam_vec hD.reverse hb zero_le_one h₀ k).trim
  have hJ0 : 0 ≤ J := by dsimp [J,normalizedPrice]; have := hD.basis; have := hD.pos; positivity
  have hI := hA.inverter (Matrix.isUnit_det_of_right_inverse h.initial.1) (increase h.flatup hγ le_rfl) h.disc
  have hC (k : Tubular _ G) : Brush j C 1 (fun y => fullCenter (Y y) k) x :=
    (beam_vec hI.reverse hJ0 zero_le_one hJ k).opposite.trim
  have hC0 : 0 ≤ C := by dsimp [C,normalizedPrice]; have := hI.basis; have := hI.pos; positivity
  have hFull : Brush j f 1 (fun y => residual (Y y) (fullCenter (Y y)) i) x :=
    (h₀ i).gathering (beam_vec hD hC0 zero_le_one hC i).trim
  have hE := treasure X.shutter hA h hγ
  have hCE (k : Tubular _ G) : Brush j Cₑ 1 (fun y =>
      (((Y y).kernelA - (Y y).plate⁻¹).transpose *ᵥ (Y y).linearBill) k) x :=
    (beam_vec hE.reverse hJ0 zero_le_one hJ k).trim
  have hCE0 : 0 ≤ Cₑ := by
    dsimp [Cₑ,normalizedPrice]
    have h1 : 0 ≤ E₀ := hE.basis
    have h2 : 0 ≤ Z+(z+Z) := hE.pos
    positivity
  have hGap : Brush j e 1 (fun y => displacement (Y y) i) x :=
    (beam_vec hD hCE0 zero_le_one hCE i).opposite.trim
  have hSq := ((hGap.paints hFull).gathering ((hGap.paints hGap).smul (1/2:ℝ)))
  apply (hSq.climb (by rw [Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/2)]; linarith) (by norm_num)).shimmy
  exact Eventually.of_forall fun y => by
    change residual (Y y) (Y y).driftM i ^ 2 / 2 - residual (Y y) (fullCenter (Y y)) i ^ 2 / 2 = _
    rw [square_difference]
    change _ + _^2/2 = _ + (1/2:ℝ)*(_*_)
    ring

end YM.Integration.PhysicalAffineScalarRows
end
