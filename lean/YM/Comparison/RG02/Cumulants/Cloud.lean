import YM.Comparison.RG02.Cumulants.Wick
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Issue.Glyph
/-!
# Exponential-moment prescription from a single Gaussian polynomial expectation

The construction uses `Rank.Normal.blend` (full Wick, `Wick.trees` for its connected
coefficients) and a *single* Gaussian covariance of the independent prescription. Here prove the
identity with genuine integration for all shifts and PSD data. Provide the total-log formula on
a shared finite mixture -- **not** disjoint/coupling-independent choices for each vertex. Both
order and covariance and vertex & leg data remain paired with one mark table. Fields may start at
grade zero in coupling (e.g., unit insertions); computations also use such nonzero mark polynomial
coefficients. This formalism supports any finite size of the color/fine field counts. No bound.
Doesn't say such a Gaussian approximates a physical law.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Cumulants
open MeasureTheory
open YM.Marker YM.Multi YM.Primitives.GCC.Anchor
open YM.Next.Rank YM.Next.SectorChange.Gaussian
open YM.Extra.Trajectories (connected connected_quiet pass_connected)
open YM.PhysicalNext.WeightedGaussianMarginal45C.Issue (realRank fullGlyph)
open Finset Function
open scoped Topology BigOperators Classical

namespace Cloud
variable {I V K : Type} [Fintype I] [DecidableEq I]
local notation "X" => I → ℝ

-- polynomial expectation for the full formal prescription, same sign conventions as Rank.Normal
-- with explicit mean. Use real gaussian integral only after h positivity.
def wick (Q : Matrix I I ℝ) (hQ : Q.IsSymm) (m : I → ℂ) : Normal.poly I →ₗ[ℂ] ℂ :=
  Normal.blend (realRank _ hQ) m
omit [Fintype I] [DecidableEq I] in
lemma wick_one (Q : Matrix I I ℝ) (hQ : Q.IsSymm) (m) : wick Q hQ m 1=1 := Normal.fresh ..

abbrev paint (x : I → ℝ) : Normal.poly I →ₐ[ℂ] ℂ := MvPolynomial.aeval (fun i=> (x i : ℂ))
def shift (m : I→ℝ) : I→ℂ := fun i=>m i
omit [Fintype I] [DecidableEq I] in
lemma shift_zero : shift (0:I→ℝ)=(0:I→ℂ) := by ext i; all_goals simp [shift]

lemma paid (Q : Matrix I I ℝ) (hQ : Q.IsSymm) (hq : Q.PosSemidef) (m : I → ℝ) (f : Normal.poly I) :
    Integrable (fun z=> paint (m+z) f) (cloud Q) ∧
      (∫ z, paint (m+z) f ∂cloud Q)=wick Q hQ (shift m) f := by
  have H := fullGlyph Q hq hQ
  exact ⟨Tapes.carries_int H m f, Tapes.payment m H f⟩

variable [DecidableEq V] {R : Census V}

/-- Concrete polynomial before the logarithm: sum over all disjoint partitions of s by marked
 drivers, each of which contributes one polynomial in the common field. In particular valid on
 the combined coupler-marker algebra in later files. -/
def integrand (p : Hot R → Normal.poly I) (s : R.Mode) : Normal.poly I :=
  ∑ t∈shards R s,∏ i∈t.val,p i

/-- Normalized Gaussian encounter with all the drivers. *Derivative grades already part of `p`*. -/
def prescription (Q : Matrix I I ℝ) (hQ : Q.IsSymm) (m : I → ℂ) (p : Hot R → Normal.poly I) :=
  Poly.inject fun s=> wick Q hQ m (integrand p s)

omit [Fintype I] [DecidableEq I] in
lemma prescribed (Q : Matrix I I ℝ) (hQ : Q.IsSymm) (m : I → ℂ) (p : Hot R → Normal.poly I) :
    prescription Q hQ m p = driven (wick Q hQ m) p := by
  ext i
  rw [driven_part]; exact map_sum (wick Q hQ m) ..

variable [Fintype V]

omit [Fintype I] [DecidableEq I] in
lemma before_log (p : Hot R→ Normal.poly I) (x : I → ℝ) (s : R.Mode) :
    paint x (integrand p s)=(Poly.pass (lit R (fun j=> paint x (p j)))).part s := by
  rw [← driven_pass,driven_part]; unfold integrand; simp_rw [map_sum, map_prod,id]

/-- Genuine finite-period Gaussian identity. Under integration only, after fixed covariance,
 including degenerate PSD. Vertex entries may read higher-leg terms with equal labels/sites. -/
lemma gaussian (Q : Matrix I I ℝ) (hQ : Q.IsSymm) (hq : Q.PosSemidef) (m : I → ℝ)
    (p : Hot R→ Normal.poly I) (s : R.Mode) :
    let F := fun z:I→ℝ => (Poly.pass (lit R (fun i=> paint (m+z) (p i)))).part s
    Integrable F (cloud Q) ∧ (∫ z,F z ∂cloud Q)=(prescription Q hQ (shift m) p).part s := by
  simp_rw [← before_log]; exact paid _ _ hq m _

omit [Fintype I] [DecidableEq I] in
/-- Provides connected Gaussian step in the output; expand each summand by the connected
 recurrence `Wick.connected_tree`, after one uses linearity to express any polynomial in
 its own ordered-leg basis. Outer factors can still correlate after this formula. -/
lemma prescribed_log (Q : Matrix I I ℝ) (hQ : Q.IsSymm) (m : I→ℂ) (p : Hot R → Normal.poly I)
    (t : R.Mode) : (connected (prescription Q hQ m p)).part t = ∑ s∈shards R t,
      (connected (moments (parts R) (wick Q hQ m) p)).part s := by
  rw [prescribed, log_driven _ p t (wick_one ..)]

section shared
variable [Fintype K]

lemma mixture_log {J : K→Type}
    (Q : ∀ k,Matrix (J k) (J k) ℝ) (hQ : ∀ k,(Q k).IsSymm) (m : ∀ k,J k→ℂ)
    (p : ∀ k,Hot R→ Normal.poly (J k)) (w : K→ℂ) (hw : ∑ i,w i=1) (t : R.Mode) :
    (connected (mix w (fun k=> prescription (Q k) (hQ k) (m k) (p k)))).part t =
      ∑ s∈shards R t,(connected (moments (parts R) (tagAverage w)
        (fun i k=> ∑ b∈shards R i.val,(connected (moments (parts R) (wick (Q k) (hQ k) (m k)) (p k))).part b))).part s := by
  rw [total_log t _ w hw]; simp_rw [prescribed_log]
  intro a; simp_rw [prescribed, driven_quiet]; exact wick_one ..
end shared
end Cloud
end YM.Comparison.RG02.Cumulants
