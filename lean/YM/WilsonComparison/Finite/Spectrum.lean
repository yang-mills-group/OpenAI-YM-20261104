import YM.AlbaMS.Cutis.Front
import YM.MS.Swirl.Mill

/-!
# Exact finite-torus spectral dictionary

No removal estimate in this file. We compute the spectral expansion of the *actual*
real-space propagator used by the Cutis finite-dimensional gauge-change theorems
at lattice unit 1, to compare to the Master in `PhysicalSum`. We keep zero modes
and their special convention (inverse zero = 0), the counting measure factor and
the midpoint phases. These lemmas up through `*_entries` concern the straight part,
BEFORE restricting to inversion-equivariant fields. All sums are on the supplied full torus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonComparison.Finite
open Function Matrix Lattice Bloch
open MS MS.Landau MS.Tone MS.Orbit MS.Swirl.Near
open MSBar MSBar.Cutis MSBar.Cutis.Winter
open scoped BigOperators Matrix ComplexOrder
open Complex (I)
variable {n : Side}

/-- Forward and reverse difference symbols in **positive link base** (not midpoint). -/
def dSymbol (p : Site n) (i : Axis) : ℂ := cell p (step i) - 1
def dStar (p : Site n) (i : Axis) : ℂ := cell p (-step i) - 1
abbrev midPhase (p : Site n) (i : Axis) : ℂ := bill (Coord p) (MS.Tone.Frame.z i)
abbrev lapSymbol (p : Site n) : ℂ := (MS.Momentum.sq (MS.Momentum.wave (Coord p)) : ℝ)

lemma step_eq_phase (p : Site n) (i : Axis) :
    cell p (step i) = midPhase p i * midPhase p i := by
  nth_rw 1 [← wrap_step n i]
  rw [← dual_cell, rights, MS.Tone.Frame.centr, rightadd]

lemma dSymbol_phase (p : Site n) (i : Axis) :
    dSymbol p i = midPhase p i * (I * (MS.Momentum.wave (Coord p) i : ℂ)) := by
  unfold dSymbol
  have h := MS.Tone.Frame.s_wave (Coord p) i
  rw [step_eq_phase, ← h, MS.Tone.inverse]
  change midPhase p i * _ - 1 = _ * (midPhase p i - (midPhase p i)⁻¹)
  rw [mul_sub, mul_inv_cancel₀ (show midPhase p i ≠ 0 from nonz _ _)]

lemma dStar_phase (p : Site n) (i : Axis) :
    dStar p i = - (midPhase p i)⁻¹ * (I * (MS.Momentum.wave (Coord p) i : ℂ)) := by
  unfold dStar
  rw [cell_inverse, step_eq_phase, _root_.mul_inv_rev, ← MS.Tone.Frame.s_wave, MS.Tone.inverse]
  change _ = -(midPhase p i)⁻¹ * (midPhase p i - (midPhase p i)⁻¹)
  rw [neg_mul, mul_sub, inv_mul_cancel₀ (show midPhase p i ≠ 0 from nonz _ _), neg_sub]

lemma dStar_dSymbol (p : Site n) (i : Axis) (j : Axis) :
    dSymbol p i * dStar p j = midPhase p i * (midPhase p j)⁻¹ *
      (((MS.Momentum.wave (Coord p) i) * (MS.Momentum.wave (Coord p) j) : ℝ) : ℂ) := by
  rw [dSymbol_phase, dStar_phase]; push_cast
  generalize midPhase p i = u, midPhase p j = v
  generalize (MS.Momentum.wave (Coord p) i : ℂ) = k, (MS.Momentum.wave (Coord p) j : ℂ) = l
  rw [show u * (I * k) * (-v⁻¹ * (I*l)) = -(I^2) * (u*v⁻¹*(k*l)) by ring,
    Complex.I_sq]; ring

lemma lapSymbol_ne {p : Site n} (hp : p ≠ 0) : lapSymbol p ≠ 0 := by
  intro h
  let q := MS.Momentum.wave (Coord p)
  change ((MS.Momentum.sq q : ℝ) : ℂ) = 0 at h
  rw [Complex.ofReal_eq_zero] at h
  obtain ⟨i,hi⟩ := step_picks p hp
  have hz : q i ^ 2 = 0 := (Finset.sum_eq_zero_iff_of_nonneg
    (s:=Finset.univ) (f:=fun i : Axis => q i ^ 2) (fun i _ => sq_nonneg (q i))).mp h i (Finset.mem_univ _)
  apply hi ∘ sub_eq_zero.mp
  change dSymbol p i = 0
  rw [dSymbol_phase]
  change _ * (_*((q i:ℝ):ℂ)) = 0
  simp [show q i = 0 by simpa using hz]

@[simp] lemma lapSymbol_zero : lapSymbol (0:Site n) = 0 := by
  rw [lapSymbol, ξ_zero]; simp [MS.Momentum.sq, MS.Momentum.wave, MS.Momentum.theta]


section Scalar
-- Cast once into complex matrices; Pose is application to one Fourier basis function.
-- Using a relation avoids carrying diagonalization assumptions out to callers.
def Pose (p : Site n) (A : Cell n) (z : ℂ) : Prop :=
  A.map Complex.ofReal *ᵥ cell p = z • cell p

namespace Pose
variable {p : Site n} {A B : Cell n} {z y : ℂ}
lemma entries (h : Pose p A z) (x : Site n) :
    ∑ i : Site n, (A x i : ℂ) * cell p i = z * cell p x := congr_fun h x
lemma of_entries (h : ∀ x : Site n, ∑ i : Site n, (A x i : ℂ) * cell p i = z * cell p x) : Pose p A z :=
  funext h
lemma one : Pose p (1 : Cell n) 1 := by simp [Pose, Matrix.map_one]
lemma zero : Pose p (0 : Cell n) 0 := by simp [Pose, Matrix.map_zero]
lemma plus (h : Pose p A z) (k : Pose p B y) : Pose p (A+B) (z+y) := by
  unfold Pose at *; rw [Matrix.map_add _ Complex.ofReal_add, Matrix.add_mulVec,h,k,add_smul]
lemma minus (h : Pose p A z) (k : Pose p B y) : Pose p (A-B) (z-y) := by
  apply of_entries; intro x
  simp_rw [Matrix.sub_apply, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib, h.entries x,k.entries x]
lemma prod (h : Pose p A z) (k : Pose p B y) : Pose p (A * B) (z*y) := by
  have he : (A*B).map ((↑) : ℝ → ℂ) = _ := Matrix.map_mul (f:=Complex.ofRealHom)
  unfold Pose at *
  rw [he, ← Matrix.mulVec_mulVec]
  change A.map Complex.ofReal *ᵥ (B.map Complex.ofReal *ᵥ _) = _
  rw [k, Matrix.mulVec_smul,h,smul_smul,mul_comm z]
lemma sum {ι : Type*} (t : Finset ι) {f : ι → Cell n} {g : ι → ℂ}
    (h : ∀ i ∈ t, Pose p (f i) (g i)) : Pose p (∑ i∈t,f i) (∑ i∈t,g i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (Pose.zero (p:=p))
  | @insert i t hi IH =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact plus (h i (Finset.mem_insert_self ..))
      (IH fun j hj => h j (Finset.mem_insert_of_mem hj))
lemma transfer (h : Pose p (A * B) z) (k : Pose p B y) (he : y ≠ 0) : Pose p A (z / y) := by
  unfold Pose at *
  rw [show (A*B).map ((↑) : ℝ → ℂ) = _ from Matrix.map_mul (f:=Complex.ofRealHom)] at h
  rw [← Matrix.mulVec_mulVec] at h
  change A.map Complex.ofReal *ᵥ (B.map Complex.ofReal *ᵥ _) = _ at h
  rw [k, Matrix.mulVec_smul] at h
  rw [← inv_smul_smul₀ he (A.map Complex.ofReal *ᵥ cell p),h,smul_smul, div_eq_mul_inv, mul_comm y⁻¹]
end Pose

lemma limo_pose (p : Site n) (x : Site n) : Pose p (limo n x) (cell p x) := by
  classical
  apply Pose.of_entries
  intro y
  simp [limo,apply_ite,ite_mul,mul_comm (cell p x)]
lemma d_pose (p : Site n) (i : Axis) : Pose p (Winter.del n i) (dSymbol p i) :=
  (limo_pose p _).minus Pose.one
lemma dStar_pose (p : Site n) (i : Axis) : Pose p (Winter.del n i)ᵀ (dStar p i) := by
  rw [Winter.del, transpose_sub, Winter.limo_t, transpose_one]
  exact (limo_pose p _).minus Pose.one
lemma lap_pose (p : Site n) : Pose p (Winter.lap n) (lapSymbol p) := by
  unfold lapSymbol MS.Momentum.sq
  rw [Complex.ofReal_sum]
  apply Pose.sum; intro i _
  have h := Pose.prod (dStar_pose p i) (d_pose p i)
  rw [mul_comm (dStar p i), dStar_dSymbol, mul_inv_cancel₀ (show midPhase p i ≠0 from nonz _ _), one_mul] at h
  simpa only [pow_two] using h
lemma nonzero_mean {p : Site n} (h : p ≠ 0) : Pose p (Winter.mean n) 0 := by
  apply Pose.of_entries; intro x
  change ∑ i : Site n, (Winter.fee n : ℂ)*cell p i= _
  rw [← Finset.mul_sum,sum_cell h,mul_zero,zero_mul]
lemma zero_mean : Pose (0:Site n) (Winter.mean n) 1 := by
  apply Pose.of_entries; intro x
  change ∑ i : Site n, (Winter.fee n : ℂ)*cell (0:Site n) i= _
  simp_rw [show ∀ i:Site n, cell 0 i=1 from fun i=> by rw [cell_duality,cell_origin]]
  rw [mul_one]
  simp_rw [mul_one, Finset.sum_const, Finset.card_univ,nsmul_eq_mul]
  rw [mul_comm]; exact_mod_cast Winter.fee_o n

lemma green_pose (p : Site n) : Pose p (Winter.green n) (lapSymbol p)⁻¹ := by
  by_cases h : p = 0
  · subst p
    have m : Pose (0:Site n) (Winter.green n * Winter.mean n) 0 := Winter.green_mean n ▸ Pose.zero
    simpa using m.transfer zero_mean one_ne_zero
  have m : Pose p (Winter.green n * Winter.lap n) 1 := by
    rw [← Winter.lap_sym, ← Winter.green_sym, ← Matrix.transpose_mul, Winter.lap_green,
      Matrix.transpose_sub,transpose_one, Winter.mean_t]
    simpa using Pose.one.minus (nonzero_mean h)
  simpa using m.transfer (lap_pose p) (lapSymbol_ne h)

lemma cell_left_neg (p x : Site n) : cell (-p) x = (cell p x)⁻¹ := by
 rw [cell_duality,cell_inverse,cell_duality x]

/-- Recover an entry from its eigenvalues with the exact counting measure conventions. -/
theorem matrix_entries {A : Cell n} {f : Site n → ℂ}
    (h : ∀ p, Pose p A (f p)) (x y : Site n) :
    (A x y : ℂ) = ∑ p : Site n, MS.Orbit.scaleZ n * cell p x * cell (-p) y * f p := by
  classical
  symm
  calc
    _ = scaleZ n * ∑ p : Site n, ((∑ u : Site n, (A x u : ℂ) * cell p u) * cell (-p) y) := by
      simp_rw [(h _).entries x]; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intros; ring
    _ = scaleZ n * ∑ u : Site n, (A x u : ℂ) * ∑ p : Site n, cell p u * cell (-p) y := by
      simp_rw [Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]
      rw [Finset.sum_comm]
    _ = _ := by
      have he (u:Site n) : (∑ p : Site n, cell p u * cell (-p) y)=
          if u=y then (n.val:ℂ)^4 else 0:= by
        simp_rw [cell_left_neg _ y, fun p : Site n => cell_duality p u, fun p : Site n => cell_duality p y]
        exact Bloch.orthogonal u y
      simp_rw [he]; rw [Finset.sum_eq_single y]
      · rw [if_pos rfl]
        unfold scaleZ νt; push_cast; field_simp [side_ne n]
      · intro b _ he; rw [if_neg he,mul_zero]
      simp
end Scalar

section Vector
-- Extract matrix blocks to reuse Pose. This pays the correct midpoint phase.
private lemma section_entries (A : Dir n) (i j : Axis) (x y : Site n) :
    (((mouth n i)ᵀ * A * mouth n j) x y) = A (x,i) (y,j) := by
  rw [cheeks, cheeks_left]
lemma block_mono (i j : Axis) :
    (mouth n i)ᵀ * mono n * mouth n j =
      ((if i=j then 1 else 0 : Cell n) * Winter.lap n) - Winter.del n i * (Winter.del n j)ᵀ := by
  unfold mono
  rw [Matrix.mul_sub, Matrix.sub_mul]
  congr 1
  · rw [Matrix.mul_assoc, pump_by, ← Matrix.mul_assoc, mouth_orth]
  rw [← Matrix.mul_assoc (mouth n i)ᵀ (bound n), eyebrow, Matrix.mul_assoc]
  rw [← transpose_transpose (mouth n j), ← Matrix.transpose_mul, eyebrow]
lemma block_W (i j : Axis) :
    (mouth n i)ᵀ * W n * mouth n j =
      green n * ((mouth n i)ᵀ * mono n * mouth n j) * green n := by
  unfold W Winter.L
  simp only [← Matrix.mul_assoc]; rw [pump_to]
  rw [Matrix.mul_assoc _ (pump n (green n)) _, pump_by, ← Matrix.mul_assoc]
lemma W_pose (p : Site n) (i j : Axis) :
    Pose p ((mouth n i)ᵀ * W n * mouth n j)
      (midPhase p i * (midPhase p j)⁻¹ *
        Tail (Landau.gauge i) (Landau.gauge j) (MS.Momentum.wave (Coord p))) := by
  rw [block_W, block_mono]
  let P:= MS.Momentum.wave (Coord p)
  let Di : ℂ := if i=j then 1 else 0
  have he : Pose p ((if i=j then 1 else 0):Cell n) Di := by
    dsimp [Di]; split <;> first| exact Pose.one|exact Pose.zero
  have h := ((green_pose p).prod ((he.prod (lap_pose p)).minus ((d_pose p i).prod (dStar_pose p j)))).prod (green_pose p)
  rw [dStar_dSymbol] at h
  refine Eq.mp ?_ h
  congr 1
  unfold Tail Landau.gauge Landau.precision Landau.delta
  by_cases hij : i=j
  · subst j; dsimp only [lapSymbol,Di]; simp only [ite_true,mul_inv_cancel₀ (show midPhase p i ≠ 0 from nonz _ _)]
    push_cast; simp_rw [div_eq_mul_inv, one_mul, ← inv_pow]; ring
  dsimp only [lapSymbol,Di]; simp only [if_neg hij]; push_cast; simp_rw [div_eq_mul_inv, ← inv_pow]; ring

lemma U_pose (p : Site n) (i : Axis) :
    Pose p ((mouth n i)ᵀ * Winter.U n) (dSymbol p i * (lapSymbol p)⁻¹) := by
  rw [Winter.U, ← Matrix.mul_assoc]; unfold Winter.L; rw [pump_to, Matrix.mul_assoc, eyebrow]
  rw [mul_comm (dSymbol _ _)]
  exact (green_pose p).prod (d_pose p i)

lemma W_entries (x y : Site n) (i j : Axis) :
    ((W n (x,i) (y,j) : ℝ) : ℂ) = ∑ p : Site n, scaleZ n * cell p x * cell (-p) y *
      (midPhase p i * (midPhase p j)⁻¹ *
        Tail (MS.Landau.gauge i) (MS.Landau.gauge j) (MS.Momentum.wave (Coord p))) := by
  rw [← section_entries (W n)]; exact matrix_entries (fun p=> W_pose p i j) x y
lemma U_entries (x y : Site n) (i : Axis) :
    ((Winter.U n (x,i) y : ℝ) : ℂ) = ∑ p : Site n, scaleZ n * cell p x * cell (-p) y *
      (midPhase p i * Tail (MS.Landau.anti i) MS.Landau.ghost (MS.Momentum.wave (Coord p))) := by
  rw [← cheeks_left n i (Winter.U n)]; rw [matrix_entries (fun p => U_pose p i)]
  refine Finset.sum_congr rfl fun p _=> ?_
  rw [dSymbol_phase, Tail]; push_cast; rw [div_eq_mul_inv]; ring
end Vector
end YM.WilsonComparison.Finite
