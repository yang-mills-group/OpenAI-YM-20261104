import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.StreamsA
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Narrow
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Street

/-! The local paired logarithm stored at a fine bond, compared at that same
bond with the logarithm of the full physical affine Gram matrix. The price
comes from the principal-window inverse discrepancy inside the Jacobi integral.
Every color at the root is retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarLogarithm
open Filter Function Lattice RG Wilson Pressure Pressure.Stores Tree Precision
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Control
open ConnectedActivityE6.Window ConnectedActivityE6.Pulse ConnectedActivityE6.Blaze
open Brush Foramen Vine Tablet ConnectedActivityE6.Census Itinerary Matrix Finset MeasureTheory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f}
  {T : Tube G S} {F : Forest S.ratio}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {j B m : ℕ} {η r Q γ v z : ℝ} {x : E}

/-- Diagonal density of the full matrix logarithm on one physical bond. -/
def full (A : Mat f G) (b : Bond f) := ∑ i : G.ColorIndex, coil A (b,i)

theorem sum_full (A : Mat f G) (hp : Torch η r Q)
    (h : Allow A (along S) m η r Q) :
    (∑ b, full A b) = Real.log A.det := by
  simpa only [full,Fintype.sum_prod_type] using (clustered A hp h).symm

def windowDifference (D : Window (along (G:=G) S) B) (A : Mat f G) (b : Bond f) :=
  ∑ i : G.ColorIndex, ∫ t in (0:ℝ)..1,
    ((A-1) * (D.pad (glide A t) - (glide A t)⁻¹)) (b,i) (b,i)

theorem difference_eq (D : Window (along (G:=G) S) B) (A : Mat f G)
    (hp : Torch η r Q) (h : Allow A (along S) m η r Q) (b : Bond f) :
    windowDifference D A b = Batch.joint A D b - full A b := by
  unfold windowDifference Batch.joint full
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  let I := Set.uIcc (0:ℝ) 1
  have h₁ : ContinuousOn (fun t => (A-1) * D.pad (glide A t)) I :=
    continuousOn_const.mul (vibrate D A h hp)
  have h₂ : ContinuousOn (fun t => (A-1) * (glide A t)⁻¹) I :=
    continuousOn_const.mul (flowing I (strung A) (fun t ht => by
      change t ∈ Set.uIcc (0:ℝ) 1 at ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      exact Matrix.isUnit_det_of_right_inverse ((h.glide hp.hv hp.hQ t ht).initial.1)))
  simp only [localBase,lact,intensity,pow_zero,mul_one,Pulse.coil,mul_sub,Matrix.sub_apply]
  exact intervalIntegral.integral_sub
    (continuousOn_pi.mp (continuousOn_pi.mp h₁ (b,i)) (b,i)).intervalIntegrable
    (continuousOn_pi.mp (continuousOn_pi.mp h₂ (b,i)) (b,i)).intervalIntegrable

def windowPrice (G : Gauge) (j B m : ℕ) (η r Q γ v : ℝ) : ℝ :=
  let a := 1+(v+1)
  let h := payE η r Q m
  (Fintype.card G.ColorIndex:ℝ) * ((v+1) *
    (token j a h * tidal γ a (facePrice j B m a h) B))

def derivativePrice (j : ℕ) (z : ℝ) : ℝ := z+(driftP j z+(z+driftP j z))

theorem window_jets (D : Window (along (G:=G) S) B) (A : E → Mat f G)
    (hp : Torch η r Q) (h : Allow (A x) (along S) m η r Q)
    (p : Tablet j γ v z A (along S) (along S) x) (hγ : γ ≤ retain η r Q) (b : Bond f) :
    Brush j (windowPrice G j B m η r Q γ v) (derivativePrice j z)
      (fun y => windowDifference D (A y) b) x := by
  let a := 1+(v+1)
  let h₀ := payE η r Q m
  let H := token j a h₀ * tidal γ a (facePrice j B m a h₀) B
  have hz : 0 ≤ derivativePrice j z := by
    unfold derivativePrice driftP
    have := p.pos
    positivity
  have hs (i : G.ColorIndex) : Brush j ((v+1)*H) (derivativePrice j z)
      (fun y => ∫ t in (0:ℝ)..1,
        ((A y-1) * (D.pad (glide (A y) t) - (glide (A y) t)⁻¹)) (b,i) (b,i)) x := by
    apply yogic
    · intro t ht
      let K (s : E × ℝ) := glide (A s.1) s.2
      have hf := joyful D A h p hp t ht
      have hi := Matrix.isUnit_det_of_right_inverse ((h.glide hp.hv hp.hQ t ht).initial.1)
      exact per_entry (fun s : E × ℝ => A s.1-1)
        (fun s => D.pad (K s) - (K s)⁻¹) (x,t) (b,i) (b,i)
        (fun k => ((p.singular (b,i) k).smooth.comp (x,t) (f:=Prod.fst) contDiffAt_fst).sub contDiffAt_const)
        (fun k => (hf k (b,i)).2.sub (jetBack (A:=K) (fun u w => (hf u w).1) hi k (b,i)))
    · intro t ht
      have hp₁ := p.joined (Tablet.fixed (1 : Mat f G) (one_pay _ _) p.scale zero_le_one p.pos).mirror
      have hp₂ := treasure D (thunder p t ht) (h.glide hp.hv hp.hQ t ht) hγ
      exact ((hp₁.tilt le_rfl le_rfl hp₂.scale (half_le_self p.scale)).enjoin hp₂).singular (b,i) (b,i)
  simpa only [windowDifference,windowPrice,a,h₀,H,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    using Brush.spree Finset.univ _ (fun _ : G.ColorIndex => (v+1)*H) hz (fun i _ => hs i)

/-- The physical log-integrand sign, including the stage's own flat tag
reference. Summing the independent full terms gives the paired half log. -/
def fullPair (X : Coat T F) (b : Bond f) : ℝ := (full X.blank.plate b - full X.plate b)/2

theorem stored (X : Coat T F) (b : Bond f) (hp : Torch η r Q)
    (h₀ : Allow X.blank.plate (along S) m η r Q) (h : Allow X.plate (along S) m η r Q) :
    X.condensation b - fullPair X b =
      (windowDifference X.shutter X.blank.plate b - windowDifference X.shutter X.plate b)/2 := by
  rw [difference_eq _ _ hp h₀,difference_eq _ _ hp h]
  unfold Coat.condensation fullPair
  ring

theorem fullPair_sum (X : Coat T F) (hp : Torch η r Q)
    (h₀ : Allow X.blank.plate (along S) m η r Q) (h : Allow X.plate (along S) m η r Q) :
    (∑ b, fullPair X b) = (Real.log X.blank.plate.det - Real.log X.plate.det)/2 := by
  unfold fullPair
  rw [← Finset.sum_div,Finset.sum_sub_distrib,sum_full _ hp h₀,sum_full _ hp h]

private theorem stored_vary (X : Coat T F) (U : Config G c) (b : Bond f) (hp : Torch η r Q)
    (h₀ : Allow X.blank.plate (along S) m η r Q)
    (h : Allow (vary X U).plate (along S) m η r Q) :
    (vary X U).condensation b - fullPair (vary X U) b =
      (1/2:ℝ) * (windowDifference X.shutter X.blank.plate b -
        windowDifference X.shutter (vary X U).plate b) := by
  have eq := stored (vary X U) b hp h₀ h
  have hD : (vary X U).shutter = X.shutter := rfl
  have hB : (vary X U).blank = X.blank := rfl
  rw [hD,hB] at eq
  have half (a : ℝ) : a/2 = (1/2:ℝ)*a := by ring
  exact eq.trans (half _)

theorem stored_jets (X : Coat T F) (U : E → Config G c) (b : Bond f) (hp : Torch η r Q)
    (h₀ : Allow X.blank.plate (along S) m η r Q)
    (h : ∀ᶠ y in 𝓝 x, Allow (vary X (U y)).plate (along S) m η r Q)
    (p : Tablet j γ v z (fun y => (vary X (U y)).plate) (along S) (along S) x)
    (hγ : γ ≤ retain η r Q)
    (p₀ : Tablet j γ v z (fun _ : E => X.blank.plate) (along S) (along S) x) :
    Brush j (windowPrice G j X.B m η r Q γ v) (derivativePrice j z)
      (fun y => (vary X (U y)).condensation b - fullPair (vary X (U y)) b) x := by
  let H := windowPrice G j X.B m η r Q γ v
  have hf := window_jets X.shutter (fun _ : E => X.blank.plate) hp h₀ p₀ hγ b
  have hg := window_jets X.shutter (fun y => (vary X (U y)).plate) hp h.self_of_nhds p hγ b
  have ht := ((hf.separating hg).smul (1/2:ℝ))
  apply (ht.climb (show ‖(1/2:ℝ)‖*(H+H) ≤ H by rw [Real.norm_of_nonneg (by norm_num)]; linarith) le_rfl).shimmy
  filter_upwards [h] with y hy
  exact stored_vary X (U y) b hp h₀ hy

end YM.Integration.PhysicalAffineScalarLogarithm
end
