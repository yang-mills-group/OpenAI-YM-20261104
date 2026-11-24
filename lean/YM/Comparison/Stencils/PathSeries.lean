import YM.UVExt.PathJet
import YM.Pert.First.PathJet
import YM.Comparison.Stencils.RaySeries

/-!
# Ordered links and any transported curvature letter

Before gauge fixing and on arbitrary (also periodic) site systems. In terms
of `PowerSeries ℂ` for component letters, from *ordered* matrix series over
real curves. Repeated/negative path edges are actual occurrences of the very
same link variables. No assumptions on faces in an integration or in a test
mask. A leading letter reads the ordinary linear oriented curl.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Stencils
open Lattice Function RG Wilson Filter Gauge CubicMatch
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators

variable {G : Gauge}
section Paths
variable {R : Type*} [AddCommGroup R] [One R]

/-- Link coordinates before any slice constraint. -/
abbrev Paper (G : Gauge) (R : Type*) := Links R G.Color

def linksOf (A : Paper G R) : Links R G.El := fun e => G.lieExp (A e)

def orientedColor (A : Paper G R) (x : Four R) (d : Step) : G.Color :=
  if d.neg then - A (d.used x) else A (d.used x)

lemma read_ray (A : Paper G R) (x : Four R) (d : Step) (t : ℝ) :
    d.read (linksOf (t • A)) x = G.lieExp (t • orientedColor A x d) := by
  unfold Step.read orientedColor; split
  · rw [smul_neg, Work.F03.exp_neg_color]; rfl
  rfl

def oneBond (A : G.Color) : PowerSeries G.Mat :=
  PowerSeries.mk (fun k => (k.factorial : ℝ)⁻¹ • (G.colorMat A)^k)

def tracePath (A : Paper G R) (x : Four R) : Walk → PowerSeries G.Mat
  | [] => 1
  | d::w => oneBond (orientedColor A x d) * tracePath A (x+d.vec) w

lemma read_smooth (A : Paper G R) (x : Four R) (d : Step) :
    ContDiff ℝ ω (fun t : ℝ => G.mat (d.read (linksOf (t • A)) x)) := by
  simp_rw [read_ray]
  exact G.exp_jet.comp (contDiff_id.smul contDiff_const)

lemma path_smooth (A : Paper G R) (x : Four R) (w : Walk) :
    ContDiff ℝ ω (fun t : ℝ => G.mat (travel (linksOf (t • A)) x w)) := by
  induction w generalizing x with
  | nil => exact contDiff_const
  | cons d w ihm =>
    simp_rw [travel, G.mat_mul]; exact (read_smooth A x d).mul (ihm _)

lemma recording_bond (A : G.Color) :
    recording (fun t => G.mat (G.lieExp (t • A))) = oneBond A := by
  ext1 k
  rw [recorded, CubicMatch.term, UVExt.Paths.ray_deriv]; simp only [zero_smul, G.mat_lieExp_zero,
    G.mat_one, one_mul, oneBond, PowerSeries.coeff_mk]

theorem recording_path (A : Paper G R) (x : Four R) (w : Walk) :
    recording (fun t => G.mat (travel (linksOf (t • A)) x w)) = tracePath A x w := by
  induction w generalizing x with
  | nil => rw [tracePath]; simp only [travel]; rw [recording_const, G.mat_one, map_one]
  | cons d w ih =>
    simp_rw [travel, G.mat_mul]
    rw [recording_mul (read_smooth A x d).contDiffAt (path_smooth ..).contDiffAt, ih]
    simp_rw [read_ray, recording_bond, tracePath]

lemma path_append (A : Paper G R) (x : Four R) (u v : Walk) :
    tracePath A x (u++v) = tracePath A x u * tracePath A (stop x u) v := by
  induction u generalizing x with
  | nil => simp [tracePath, stop]
  | cons d w ih => simp only [List.cons_append, tracePath, stop, ih, mul_assoc]

lemma trace_zero (A : Paper G R) (x : Four R) (w : Walk) :
    PowerSeries.coeff 0 (tracePath A x w) = 1 := by
  induction w generalizing x with
  | nil => simp [tracePath]
  | cons d w ih =>
    rw [tracePath, PowerSeries.coeff_mul]; simp only [Finset.Nat.antidiagonal_zero,
      Finset.sum_singleton, oneBond, PowerSeries.coeff_mk, ih]; simp

lemma trace_leading (A : Paper G R) (x : Four R) (w : Walk) :
    PowerSeries.coeff 1 (tracePath A x w) = G.colorMat (Exterior.linkSum A x w) := by
  induction w generalizing x with
  | nil => simp [tracePath, Exterior.linkSum]
  | cons d w ih =>
    rw [tracePath, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ]
    simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, ih, trace_zero,
      oneBond, PowerSeries.coeff_mk]
    change _ = G.colorMat (orientedColor A x d + _)
    simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
      pow_zero, pow_one, one_mul, mul_one, Nat.zero_add, map_add]
    rw [add_comm]

lemma trace_flip (A : Paper G R) (x : Four R) (w : Walk) :
    tracePath A (stop x w) (Lattice.reverse w) =
      PowerSeries.mk (fun k => star (PowerSeries.coeff k (tracePath A x w))) := by
  rw [← recording_path]
  simp_rw [travel_reverse, G.mat_inv]
  let L : G.Mat →L[ℝ] G.Mat := (starL ℝ).toContinuousLinearMap
  change recording (fun t => L _) = _
  refine (recording_linear L (path_smooth A x w).contDiffAt).trans ?_
  rw [recording_path]
  rfl

/-- Paths converted as a unit. Keeping `x+d.vec` on the recursive
leg ensures that pullback on both labels and sites uses the same orientation. -/
def pullLogs (A : Paper G R) (s : Signed) (b : Four R) : Paper G R :=
  fun e => orientedColor A (affine s b e.1) ((posDir e.2).rotate s)

lemma turned (A : Paper G R) (s : Signed) (b : Four R) (t : ℝ) :
    linksOf (t • pullLogs A s b) = pull s b (linksOf (t • A)) := by
  funext e; exact (read_ray ..).symm

theorem turned_trace (A : Paper G R) (s : Signed) (b x : Four R) (w : Walk) :
    tracePath (pullLogs A s b) x w = tracePath A (affine s b x) (w.map (·.rotate s)) := by
  rw [← recording_path, ← recording_path]; simp_rw [turned, travel_pull]
end Paths

/-- Actual letter path. Account for the transport twice in using the
`tracePath` algorithm: `Slot.length` in the activity budget would instead
count the connector once. -/
def closes (s : Slot) := s.walk ++ square s.plaq.val.1 s.plaq.val.2 ++ Lattice.reverse s.walk

lemma cost_path (s : Slot) : (closes s).length = s.length + s.walk.length := by
  simp [closes, Lattice.reverse, Slot.length, square]; omega

lemma closure_path (s : Slot) : stop (0 : Cover) (closes s) = 0 := by
  rw [closes, stop_append, stop_append, square_stop, reverse_stop]

/-- Linear projection applied in real coordinates, then embedded into complex
coefficients. -/
def decode (i : G.ColorIndex) : G.Mat →L[ℝ] ℂ :=
  Complex.ofRealCLM ∘L EuclideanSpace.proj i ∘L Pert.First.recoverL G

def scalarSlot (s : Slot) (i : G.ColorIndex) (U : CoverConfig G) :=
  ((s.eval U i : ℝ) : ℂ)

theorem close_reads (s : Slot) (i : G.ColorIndex) (U : CoverConfig G) :
    scalarSlot s i U = decode i (G.mat (travel U 0 (closes s))) := by
  rw [closes, travel_append, travel_append, stop_append, square_stop, travel_reverse]
  change ↑(G.adjoint _ _ i) = ((Pert.First.recoverL G _ i : ℝ) : ℂ)
  rw [← Pert.First.recover_group, G.curvature_conjugate]; rfl

lemma slot_smooth (A : Links ℤ G.Color) (s : Slot) (i : G.ColorIndex) :
    ContDiff ℝ ω (fun t : ℝ => scalarSlot s i (linksOf (t • A))) := by
  simp_rw [close_reads]; exact (decode i).contDiff.comp (path_smooth ..)

lemma decode_mat (i : G.ColorIndex) (x : G.Color) : decode i (G.colorMat x) = (x i : ℂ) := by
  have hx : (1/2:ℝ) • (G.colorMat x - star (G.colorMat x)) = G.colorMat x := by
    rw [G.colorMat_skew, sub_neg_eq_add, ← two_smul ℝ, smul_smul]
    norm_num
  change ((G.projectColor ((1/2:ℝ) • _) i : ℝ) : ℂ) = _
  change ((G.projectColor ((1/2:ℝ) • (G.colorMat x - star (G.colorMat x))) i : ℝ) : ℂ) = _
  rw [hx, G.project_colorMat]

lemma decode_zero (i : G.ColorIndex) : decode i 1 = 0 := by
  change (↑(G.projectColor ((1/2:ℝ) • (1 - (star (1:G.Mat)))) i) : ℂ) = _
  simp only [star_one, sub_self, smul_zero, map_zero]; exact Complex.ofReal_zero

/-- Formal unmasked slot vertex, *including* the one slot-coupling
normalization. In particular its constant term is linear in the link field,
not the value of the curvature variable at the identity. -/
def slotSeries (A : Links ℤ G.Color) (s : Slot) (i : G.ColorIndex) : PowerSeries ℂ :=
  PowerSeries.mk (fun k => decode i (PowerSeries.coeff (k+1) (tracePath A 0 (closes s))))

theorem recording_slot (A : Links ℤ G.Color) (s : Slot) (i : G.ColorIndex) :
    recording (fun t : ℝ => scalarSlot s i (linksOf (t • A))) = PowerSeries.X * slotSeries A s i := by
  simp_rw [close_reads]
  refine (recording_linear (decode i) (path_smooth A 0 (closes s)).contDiffAt).trans ?_
  rw [recording_path]
  apply PowerSeries.ext
  intro k
  cases k with
  | zero =>
    rw [PowerSeries.coeff_mk]
    change decode i (PowerSeries.coeff 0 (tracePath A 0 (closes s))) = _
    rw [trace_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [map_mul, PowerSeries.constantCoeff_X, zero_mul]
    exact decode_zero i
  | succ k => simp only [PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul, slotSeries]; rfl

lemma trace_starts (A : Links ℤ G.Color) (s : Slot) :
    PowerSeries.coeff 1 (tracePath A 0 (closes s)) =
      G.colorMat (Exterior.linkSum A s.offset (square s.plaq.val.1 s.plaq.val.2)) := by
  let f := tracePath A 0 s.walk
  let k := square s.plaq.val.1 s.plaq.val.2
  let g := tracePath A s.offset k
  have h₀ (a b : PowerSeries G.Mat) : PowerSeries.coeff 0 (a*b) =
      PowerSeries.coeff 0 a * PowerSeries.coeff 0 b := by rw [PowerSeries.coeff_mul]; simp
  have h₁ (a b : PowerSeries G.Mat) : PowerSeries.coeff 1 (a*b) =
      PowerSeries.coeff 0 a * PowerSeries.coeff 1 b +
        PowerSeries.coeff 1 a * PowerSeries.coeff 0 b := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ]; simp
  rw [closes, path_append, path_append, stop_append, square_stop, trace_flip]
  change PowerSeries.coeff 1 (f*g*PowerSeries.mk _) = _
  rw [h₁, h₀ f g, h₁ f g]
  simp only [f,g,PowerSeries.coeff_mk, trace_zero, trace_leading, G.colorMat_skew,
    one_mul, mul_one, star_one]
  change - _ + (_+_) = G.colorMat (Exterior.linkSum A s.offset k)
  abel

theorem slot_linear (A : Links ℤ G.Color) (s : Slot) (i : G.ColorIndex) :
    PowerSeries.coeff 0 (slotSeries A s i) =
      ((Exterior.linkSum A s.offset (square s.plaq.val.1 s.plaq.val.2) i : ℝ) : ℂ) := by
  rw [slotSeries, PowerSeries.coeff_mk, trace_starts, decode_mat]

/-- Use locality from the *unnormalized* data even for the normalized
series coefficients. -/
theorem slot_local (s : Slot) (i : G.ColorIndex) :
    LocalOn s.stencil (fun A => slotSeries A s i) := by
  intro A B H
  apply PowerSeries.X_pow_mul_cancel (k := 1)
  rw [pow_one, ← recording_slot, ← recording_slot]
  apply congrArg recording; funext t
  have he : s.eval (linksOf (t • A)) = s.eval (linksOf (t • B)) :=
    s.covered _ _ fun l hl hl' => by simp only [linksOf, Pi.smul_apply]; rw [H l hl hl']
  exact congrArg (fun u : G.Color => (u i : ℂ)) he
end YM.Comparison.Stencils
