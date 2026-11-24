import YM.Gauge.Casimir
import YM.Extra.ITERATION_NO_LOSS.Calibration
import YM.Comparison.RG02.Assembly.Vertices
import YM.Integration.NativePaidKineticTest
import YM.Integration.RunRG02Along

/-!
# A normalized kinetic test on an actual bond

The field has one bond and one physical color.  Its norm and sum of bond
norms are exactly one, independently of the period.  The native oriented
plaquette at the origin has curvature coordinate one as soon as the
period is at least three.  The original Run's sizeT supplies this condition.

The main-term jet is the factorial-normalized jet of the full original
mainTerm composed with represent.  Its value is one half of the same Bed
quadratic form; the reciprocal estimate retains that factor two.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativeNormalizedBondTest
open Lattice Exterior Matrix RG Precision Stationary Bloch
open RG08 RG08.Supplies PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology ContDiff Matrix.Norms.Frobenius

def anchor (n : Side) : Body 1 n := (0, coord (0 : Axis))
def faceAxes : PlaqAxes := ⟨((0 : Axis), (1 : Axis)), by decide⟩
def testFace (n : Side) : Body 2 n := (0, plaquette faceAxes)
def scalarBond (n : Side) : form 1 n := fun e => if e = anchor n then 1 else 0
def scalarCurl (n : Side) : form 2 n := d 1 n *ᵥ scalarBond n
def colorUnit (G : Gauge) (k : G.ColorIndex) : G.Color := EuclideanSpace.single k 1
def bondField (G : Gauge) (n : Side) (k : G.ColorIndex) : fieldDir G n 1 :=
  fun e => scalarBond n e • colorUnit G k

private lemma color_apply (G : Gauge) (k j : G.ColorIndex) :
    colorUnit G k j = if j = k then 1 else 0 := by
  simp [colorUnit]

private lemma color_norm (G : Gauge) (k : G.ColorIndex) : ‖colorUnit G k‖ = 1 := by
  simp [colorUnit]

/-- The color is normalized physically; its matrix norm retains the gauge scale. -/
theorem matrix_color_norm (G : Gauge) (k : G.ColorIndex) :
    ‖G.colorMat (colorUnit G k)‖ = G.colorScale := by
  rw [G.colorMat_norm, color_norm, mul_one]

/-- The last term in the original oriented plaquette is the occupied bond. -/
theorem scalar_coordinate (n : Side) (hn : 3 ≤ n.val) :
    scalarCurl n (testFace n) = 1 := by
  have hstep : (step (1 : Axis) : Site n) ≠ 0 := by
    intro h
    have h1 : (1 : Per n) = 0 := by
      simpa only [step_apply, ite_true, Pi.zero_apply] using congrFun h (1 : Axis)
    have hmod := ZMod.one_eq_zero_iff.mp h1
    omega
  change (d 1 n *ᵥ scalarBond n) (0, plaquette faceAxes) = 1
  rw [d_plaquettes]
  norm_num [scalarBond, anchor, faceAxes, coord_iff, hstep]

theorem field_parts (G : Gauge) (n : Side) (k j : G.ColorIndex) :
    parts G 1 (bondField G n k) j = if j = k then scalarBond n else 0 := by
  funext e
  change scalarBond n e * colorUnit G k j = (if j = k then scalarBond n else 0) e
  rw [color_apply]
  by_cases h : j = k
  · simp only [if_pos h, mul_one]
  · simp only [if_neg h, mul_zero, Pi.zero_apply]

theorem field_off (G : Gauge) (n : Side) (k : G.ColorIndex)
    (e : Body 1 n) (he : e ≠ anchor n) : bondField G n k e = 0 := by
  simp only [bondField, scalarBond, if_neg he, zero_smul]

theorem field_norm (G : Gauge) (n : Side) (k : G.ColorIndex) :
    ‖bondField G n k‖ = 1 := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
    intro e
    by_cases h : e = anchor n
    · simpa only [bondField, scalarBond, if_pos h, one_smul, color_norm]
        using (le_refl (1 : ℝ))
    · simpa only [bondField, scalarBond, if_neg h, zero_smul, norm_zero]
        using (zero_le_one : (0 : ℝ) ≤ 1)
  · simpa only [bondField, scalarBond, ite_true, one_smul, color_norm]
      using norm_le_pi_norm (bondField G n k) (anchor n)

theorem field_sum_norm (G : Gauge) (n : Side) (k : G.ColorIndex) :
    (∑ e : Body 1 n, ‖bondField G n k e‖) = 1 := by
  calc
    _ = ‖bondField G n k (anchor n)‖ := by
      apply Finset.sum_eq_single (anchor n)
      · intro e _ he
        rw [field_off G n k e he, norm_zero]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    _ = 1 := by simp only [bondField, scalarBond, ite_true, one_smul, color_norm]

theorem field_curvature (G : Gauge) (n : Side) (hn : 3 ≤ n.val) (k : G.ColorIndex) :
    dColor G n 1 (bondField G n k) (testFace n) = colorUnit G k := by
  ext j
  change (d 1 n *ᵥ parts G 1 (bondField G n k) j) (testFace n) = colorUnit G k j
  rw [field_parts, color_apply]
  by_cases h : j = k
  · simp only [if_pos h]
    exact scalar_coordinate n hn
  · simp only [if_neg h, mulVec_zero, Pi.zero_apply]

/-- This is the derivative of the original exponential plaquette. -/
theorem plaquette_derivative (G : Gauge) (n : Side) (hn : 3 ≤ n.val) (k : G.ColorIndex) :
    HasDerivAt (fun t : ℝ =>
      G.mat (Lattice.faceValue (Precision.represent (t • bondField G n k)) (0, faceAxes)))
      (G.colorMat (colorUnit G k)) 0 := by
  have h := Work.F03.face_deriv (0, faceAxes) (bondField G n k)
  change HasDerivAt _ (G.colorMat (dColor G n 1 (bondField G n k) (testFace n))) 0 at h
  rw [field_curvature G n hn k] at h
  exact h

/-- The same real curvature vector appears in the complete colored kinetic form. -/
theorem fiscal (G : Gauge) (n : Side) (k : G.ColorIndex) (H : Bed) :
    Bid.gaugeFiscal H (bondField G n k) (bondField G n k) =
      scalarCurl n ⬝ᵥ (H.metric.acts n *ᵥ scalarCurl n) := by
  rw [Extra.Iteration.Channel.fiscal_flux]
  have h (j : G.ColorIndex) :
      (d 1 n *ᵥ parts G 1 (bondField G n k) j) ⬝ᵥ
        (H.metric.acts n *ᵥ (d 1 n *ᵥ parts G 1 (bondField G n k) j)) =
      if j = k then scalarCurl n ⬝ᵥ (H.metric.acts n *ᵥ scalarCurl n) else 0 := by
    by_cases hj : j = k
    · simp only [field_parts, if_pos hj]
      rfl
    · simp only [field_parts, if_neg hj, mulVec_zero, zero_dotProduct]
  simp only [h]
  simp

/-- Full mainTerm, with exactly the original factorial-normalized second jet. -/
theorem main_jet {G : Gauge} {n : Side} {H : Bed} {W : PathData G}
    {p : Clip} {σ C Λ u v : ℝ} (hb : W.Bounds p σ C Λ)
    (ht : Attached H W) (hf : Floor H p n u v) (hs : Bid.Sworn H n G)
    (B : fieldDir G n 1) :
    Comparison.RG02.Assembly.jet
      (fun A : fieldDir G n 1 => Precision.mainTerm p W (Precision.represent A)) 2 B =
      Bid.gaugeFiscal H B B / 2 := by
  let F := fun A : fieldDir G n 1 => Precision.mainTerm p W (Precision.represent A)
  have hsm : ContDiffAt ℝ 2 F 0 :=
    (Extra.Iteration.Calibration.main_jet (n := n) hb).of_le le_top
  have hsym (x y : fieldDir G n 1) : Bid.gaugeFiscal H x y = Bid.gaugeFiscal H y x := by
    rw [Extra.Iteration.Channel.fiscal_flux, Extra.Iteration.Channel.fiscal_flux]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (H.metric.acts n *ᵥ (d 1 n *ᵥ parts G 1 x j)) ⬝ᵥ
          (d 1 n *ᵥ parts G 1 y j) := by
        rw [dotProduct_mulVec, ← mulVec_transpose, hf.symmetric.1]
      _ = _ := dotProduct_comm _ _
  have hh := Work.F03.hessian_of_limit (f := F) (Q := Bid.gaugeFiscal H) hsm
    (fun x => Work.F03.main_limit hb ht hf hs x)
    (fun x y z => Work.F03.gaugeFiscal_add x y z) hsym
  have hvec : (fun _ : Fin 2 => B) = ![B, B] := by
    funext j
    fin_cases j <;> rfl
  change (2 : ℝ)⁻¹ * iteratedFDeriv ℝ 2 F 0 (fun _ => B) = Bid.gaugeFiscal H B B / 2
  rw [hvec, hh.2.2 B B, div_eq_mul_inv]
  exact mul_comm _ _

def colorIndex (G : Gauge) (hG : G.Simple) : G.ColorIndex := ⟨0, by
  letI := hG.nontrivial_color
  change 0 < Module.finrank ℝ G.Alg
  rw [← G.colorIso.finrank_eq]
  exact Module.finrank_pos⟩

def normalizedField (G : Gauge) (hG : G.Simple) (n : Side) : fieldDir G n 1 :=
  bondField G n (colorIndex G hG)

/-- No nonzero-test assumption: the one-bond test is constructed explicitly. -/
theorem paid_main_jet {G : Gauge} (hG : G.Simple) {a : Levels G} {H : Horizon a}
    {P X : MapPrices} {Z : ChartRatio G} (hH : H.Suffices P)
    (hpaid : Yamen.Payment G P X Z a) (N i : ℕ) (hi : i < N)
    (n : Side) (hn : 3 ≤ n.val) {W : PathData G} {σ C Λ : ℝ}
    (hb : W.Bounds (a.params (i+1)).clip σ C Λ)
    (ht : Attached (H.H N (i+1)) W) (hs : Bid.Sworn (H.H N (i+1)) n G) :
    let J := Comparison.RG02.Assembly.jet
      (fun A : fieldDir G n 1 => Precision.mainTerm (a.params (i+1)).clip W
        (Precision.represent A)) 2 (normalizedField G hG n)
    0 < J ∧ J⁻¹ ≤ 2 * ((Fintype.card (TypeFace 2) : ℝ) * Real.log (a.clock.hatBeta i)) := by
  dsimp only
  have he := NativePaidKineticTest.kinetic_reciprocal hH hpaid N i hi n
    (testFace n) (scalarCurl n) (scalar_coordinate n hn)
  have hj := main_jet hb ht (hH.all N (i+1) hi n) hs (normalizedField G hG n)
  change _ = Bid.gaugeFiscal (H.H N (i+1))
    (bondField G n (colorIndex G hG)) (bondField G n (colorIndex G hG)) / 2 at hj
  rw [fiscal] at hj
  simp only [hj]
  refine ⟨div_pos he.1 (by norm_num), ?_⟩
  rw [inv_div, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left he.2 (by norm_num : (0 : ℝ) ≤ 2)

/-- The original sizeT bound is stronger than the required period condition. -/
theorem actual_size {G : Gauge} (R : Run G) (m p : ℕ) :
    3 ≤ (R.family.side m p).val := by
  have h := R.family.path.levels.fits.sizeT m p
  change 100 * (R.family.path.levels.clock.coverSize m + 1) ≤ (R.family.side m p).val at h
  omega

def actualField {G : Gauge} (R : Run G) (hG : G.Simple) (m p : ℕ) :
    fieldDir G (R.family.side m p) 1 := normalizedField G hG (R.family.side m p)

/-- Every actual period has the same normalized, one-bond, genuine curvature test. -/
theorem actual_facts {G : Gauge} (R : Run G) (hG : G.Simple) (m p : ℕ) :
    ‖actualField R hG m p‖ = 1 ∧
    (∑ e, ‖actualField R hG m p e‖) = 1 ∧
    (∀ e, e ≠ anchor (R.family.side m p) → actualField R hG m p e = 0) ∧
    dColor G (R.family.side m p) 1 (actualField R hG m p)
      (testFace (R.family.side m p)) (colorIndex G hG) = 1 := by
  refine ⟨field_norm G _ _, field_sum_norm G _ _, field_off G _ _, ?_⟩
  change dColor G (R.family.side m p) 1
    (bondField G (R.family.side m p) (colorIndex G hG))
    (testFace (R.family.side m p)) (colorIndex G hG) = 1
  rw [field_curvature G _ (actual_size R m p)]
  exact (color_apply G (colorIndex G hG) (colorIndex G hG)).trans (if_pos rfl)

end YM.Integration.NativeNormalizedBondTest
end
