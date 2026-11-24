import YM.RG06.Weak.Path
import YM.Pert.Lattice.Readers
import YM.Pert.First.PathJet

/-!
# `seriesLex`, now with independent bare path coefficients

Works to arbitrary fixed order, any j, positions on any side.
Uses the actual hypercube rotations and curvature projection of
`tensorJet`. Coupling prefactor, h^(-(j+2)), factorial j!, path
orientations and Haar-vs-color normalization not absorbed into the
operator basis.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 220000
set_option maxRecDepth 5000
noncomputable section
namespace YM.RG06.Weak
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
open Lattice Function Pert Bare
variable {R : Type*} [AddCommGroup R] [One R] {G : Gauge} {j : ℕ}

/-- Path coefficient read of group curvature, no Bianchi conversion. -/
def skew (F : ℕ→G.Mat) := First.recoverL G ∘ F

theorem Writes.curved {p : ℝ→G.El} {F : ℕ→ G.Mat} (h : Writes (G.mat ∘ p) F) : Writes (G.curvature ∘ p) (skew F):= by
  convert! h.apply (First.recoverL G) using 1

def transport (F : ℕ→G.Mat) (V : ℕ→G.Color) :=
  (G.projectColor ∘ (join (join F (G.colorMat ∘ V)) (back F)))

theorem Writes.transport {p : ℝ→ G.El} {P : ℕ→G.Mat} {a : ℝ→G.Color} {A : ℕ→G.Color} (h : Writes (G.mat ∘ p) P) (hv : Writes a A) : Writes (fun t=> G.adjoint (p t) (a t)) (Weak.transport P A) := by
  have hT := h.backwards; simp only [G.mat_inv] at hT
  exact ((h.times (Writes.linear G.colorMat hv)).times hT).linear G.projectColor

def plateSeries (F : Links R (ℕ→ G.Mat)) (x : Four R) (k : Walk) (i a : Axis) :=
  transport (cycleWith F x k) (skew (cycleWith F (stop x k) (square i a)))

def tiled {R : Type*} (f : ℝ → Links R G.El) (F : Links R (ℕ→G.Mat)) :=
    ∀ i,Writes (fun t=>G.mat (f t i)) (F i)

theorem plateSeries_honest {f : ℝ → Links R G.El} {F : Links R (ℕ → G.Mat)} (h : tiled f F)
    (x : Four R) (k : Walk) (i a : Axis) : Writes (fun t => plateU (f t) x k i a) (plateSeries F x k i a) := by
  exact Writes.transport (p:=fun t:ℝ=>travel (f t) x k) (Writes.travel h x k)
    (Writes.curved (p:=fun t=>travel (f t) (stop x k) (square i a)) (Writes.travel h ..))

def differences (j : ℕ) (F : Links R (ℕ → G.Mat)) (x : Four R) (n : ℕ) : Response G j :=
  fun i k γ => (j.factorial:ℝ)⁻¹ • ∑ s, Bare.sign s • plateSeries F x (walk γ s) i k n

lemma differs {f : ℝ → Links R G.El} {F : Links R (ℕ → G.Mat)} (h : tiled f F)
    (x : Four R) (i k : Axis) (γ : Fin j→Axis) : Writes (fun t => diffU j (f t) x i k γ) (fun n=> differences j F x n i k γ) := by
  let he (s:Finset (Fin j)) := (plateSeries_honest h x (walk γ s) i k).scale (Bare.sign s)
  have hx := Writes.scale (j.factorial:ℝ)⁻¹ (Writes.collect Finset.univ (fun s _=>he s))
  convert! hx using 1 <;> (funext t; simp [diffU,differences,Finset.sum_apply])

lemma stamps {f : ℝ → Links R G.El} {F : Links R (ℕ → G.Mat)} (h : tiled f F)
    (j : ℕ) (x : Four R) : Writes (fun t => diffU j (f t) x) (differences j F x) := by
  exact Writes.pack (fun i=> Writes.pack (fun k=> Writes.pack (fun γ=> differs h x i k γ)))

def raw (j : ℕ) (m : ℝ) (F : Links R (ℕ → G.Mat)) (x : Four R) :=
    m^(-(j+2:ℤ)) • (radialMap (G:=G) ∘ differences j F x)

theorem raw_honest {f : ℝ → Links R G.El} {F : Links R (ℕ → G.Mat)} (h : tiled f F)
    (m : ℝ) (x : Four R) (j : ℕ) : Writes (fun t=>rawJet m (f t) x j) (raw j m F x) := by
  let L := (radialMap (G:=G) (j:=j)).toContinuousLinearMap
  exact (Writes.apply (E:=Response G j) (D:=Labels.Taylor G j) L (stamps h j x)).scale (m^(-(j+2:ℤ)))

/-- On the fine roots take the same signed `pull`, reversing the
coefficients of any reversed link before applying the path read. -/
def orient (s : Signed) (F : Links R (ℕ → G.Mat)) (b : Four R) : Links R (ℕ → G.Mat) := fun i=>
    let d := (posDir i.2).rotate s
    turn d.neg (F (d.used (affine s b i.1)))

lemma tiled.pull {f : ℝ→Links R G.El} {F : Links R (ℕ → G.Mat)} (h : tiled f F)
    (s : Signed) (b : Four R) : tiled (Lattice.pull s b ∘ f) (orient s F b) := by
  intro i
  let d: Lattice.Step:= (posDir i.2).rotate s
  exact (h (d.used (affine s b i.1))).reverse d.neg

def symjet (j : ℕ) (m : ℝ) (F : Links R (ℕ → G.Mat)) (x : Four R) (n : ℕ) :=
  (Fintype.card Signed : ℝ)⁻¹ • ∑ s : Signed,
    Labels.Taylor.turn (G:=G) (j:=j) s.ortho (raw j m (orient s F 0) (affine s⁻¹ 0 x) n)

theorem symjet_honest {f : ℝ → Links R G.El} {F : Links R (ℕ → G.Mat)} (h : tiled f F) (m : ℝ) (x : Four R) (j : ℕ) : Writes (fun t=>tensorJet m (f t) x j) (symjet j m F x) := by
  let O := fun (s:Signed) (t:ℝ)=>oval s m (f t) x j
  let V := fun (s:Signed) (n:ℕ)=> Labels.Taylor.turn (G:=G) (j:=j) s.ortho (raw j m (orient s F 0) (affine s⁻¹ 0 x) n)
  let Z (s:Signed) := (Labels.Taylor.turn (G:=G) (j:=j) s.ortho).toContinuousLinearMap
  have he (s:Signed):=(raw_honest (h.pull s 0) m (affine s⁻¹ 0 x) j).apply (Z s)
  have ht (s:Signed) : Writes (O s) (V s):=he s
  unfold tensorJet symjet
  generalize (Finset.univ (α:=Signed))=e
  exact Writes.weightedSum (g:=O) (H:=V) e _ (fun s _=>ht s)
omit [AddCommGroup R] [One R] in
lemma ray_tiled (a : Links R G.Color) : tiled (ray a) (tile a) := fun i=>matrix_reads (a i)

def coordinate (i : Labels.Key G): Labels.Taylor G i.1→L[ℝ]ℂ :=
  Complex.ofRealCLM.comp ((Labels.axes G i.1).coord i.2).toContinuousLinearMap

def boson (i : Labels.Key G) (m : ℝ) (F : Links R (ℕ → G.Mat)) (x : Four R) :=
  coordinate i ∘ symjet i.1 m F x

theorem boson_honest (i : Labels.Key G) {f : ℝ → Links R G.El} {F : Links R (ℕ → G.Mat)} (h : tiled f F) (m : ℝ) (x : Four R) :
    Writes (fun t=> Labels.coord (fun j=> tensorJet m (f t) x j) i) (boson i m F x):=by exact (symjet_honest h m x i.1).apply (coordinate i)

open Orb

theorem datum_honest (i : Labels.Key G) {n : Side} (a : Potential G n) (m : ℝ) (o : Site n) :
    Writes (fun t : ℝ=> datum m o i (t • a)) (boson i m (tile a.val) o) :=
  boson_honest i (ray_tiled a.val) m o

/-- Arbitrary coefficient of `seriesLex` (note successor: formal slot
division before any expectation). -/
theorem lex_honest (i : Labels.Key G) {n : Side} (a : Coords G n) (m : ℝ) (o : Site n) (k : ℕ) :
    PowerSeries.coeff k (seriesLex m o a i) = boson i m (tile (expand G n a).val) o (k+1) := by
  unfold seriesLex; rw [PowerSeries.coeff_mk]
  have he:= (datum_honest i (expand G n a) m o).coeff (k+1)
  rw [Next.Foundations.iteratedDeriv_on_line ((datum_diff m o i).of_le le_top)] at he
  exact he
end YM.RG06.Weak
