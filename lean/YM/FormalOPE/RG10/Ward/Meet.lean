import YM.FormalOPE.RG10.Ward.FiberCalculus
import Mathlib.Analysis.InnerProductSpace.Trace

/-! Invariance and support accounting BEFORE equation nulls. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.InversionWard
open Gauge Lattice RG Wilson MeasureTheory Metric Finset
open PertExtension PertExtension.Orb Function
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {n : Side} (b : Edge (Site n))

def carrying (X : Config G n → G.Color) :=
  ∀ t : Site n → G.El, evenAt t → ∀ U, X (Lattice.gauge t U) = G.adjoint (t b.1) (X U)
variable {X : Config G n → G.Color} {t : Site n → G.El} {U : Config G n} (hs : Proxy X) (hx : carrying b X)

include hs hx in
theorem carrying_vary (h : evenAt t) (a : G.Color) :
    vary b X (Lattice.gauge t U) (G.adjoint (t b.1) a) = G.adjoint (t b.1) (vary b X U a) := by
  let L := LinearMap.toContinuousLinearMap (G.adjoint (t b.1))
  apply (hs.derivative b (gauge t U) _).unique
  simp_rw [← map_smul, tilt_gauge b t h, hx _ h]
  exact L.hasFDerivAt.comp_hasDerivAt 0 (hs.derivative b U a)

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

theorem respects_vary {f : Config G n → M} (hf : Proxy f) (he : respects f) (ht : evenAt t) (a : G.Color) :
    vary b f (Lattice.gauge t U) (G.adjoint (t b.1) a) = vary b f U a := by
  apply (hf.derivative b (gauge t U) _).unique
  simp_rw [← map_smul, tilt_gauge b t ht, he _ ht]; exact hf.derivative b U a

include hx in
lemma respects_coupled {f : Config G n → M} (hf : Proxy f) (he : respects f) : respects (coupled b X f) := by
  intro t ht U; rw [coupled, hx _ ht]; exact respects_vary b hf he ht (X U)

lemma fallout_basis (X : Config G n → G.Color) (B : OrthonormalBasis G.ColorIndex ℝ G.Color) (U) :
    fallout b X U = ∑ i : G.ColorIndex, Inner.inner ℝ (B i) (vary b X U (B i)) := by
  unfold fallout
  change ∑ i : G.ColorIndex, Inner.inner ℝ (WardBin.dirs G i) ((vary b X U).toLinearMap (WardBin.dirs G i)) =
    ∑ i : G.ColorIndex, Inner.inner ℝ (B i) ((vary b X U).toLinearMap (B i))
  rw [← LinearMap.trace_eq_sum_inner, ← LinearMap.trace_eq_sum_inner]

include hx hs in
theorem respects_fallout : respects (fallout b X) := by
  intro t ht U
  let L := WardBin.adjointGauge (t b.1)
  let B := (WardBin.dirs G).map L
  rw [fallout_basis b X B, fallout]
  apply sum_congr rfl; intro i _
  rw [show B i = G.adjoint (t b.1) (WardBin.dirs G i) from by unfold B; rw [OrthonormalBasis.map_apply]; rfl, carrying_vary b hs hx ht]
  exact L.inner_map_map ..

lemma carrying_force : carrying b (fun U : Config G n => WardBin.euler U b) :=
    fun _ _ _ => WardBin.euler_gauge ..
lemma proxy_force : Proxy (fun U : Config G n => WardBin.euler U b) := by
  let p (i : Axis) := fun U : Config G n => G.curvature (WardBin.wheel b (posDir i) U)+ G.curvature (WardBin.wheel b (negDir i) U)
  let B := Finset.univ.filter fun k => k ≠ b.2
  have h (i : Axis) : Proxy (p i) :=
    Proxy.add (proxy_curvature (proxy_path ..)) (proxy_curvature (proxy_path ..))
  convert Proxy.sum B (f:=p) (fun i _ => h i) using 1
  funext U; rw [Finset.sum_apply]; rfl

/-- Geometric off-support condition on the *whole torus*, includes inversion clearance. -/
def off (s : Set (Site n)) : Prop :=
    (b.1∉s ∨ b.1 + step b.2∉s) ∧
    ((Orb.reflect b).1∉s ∨ (Orb.reflect b).1 + step (Orb.reflect b).2∉s)

omit [NormedAddCommGroup M] [NormedSpace ℝ M] in
lemma isolated_outside {f : Config G n → M} {s : Set (Site n)} (h : LocalOn s f) (u : off b s)
    (U : Config G n) (a : G.Color) : f (tilt b U a) = f U := by
  apply h; intro i hi hk
  unfold tilt InversionWard.push; split
  · rename_i H; subst i; exact (u.1.elim (fun hn => hn hi) (fun hn => hn hk)).elim
  split
  · rename_i H; subst i; exact (u.2.elim (fun hn => hn hi) (fun hn => hn hk)).elim
  rfl

lemma isolated {f : Config G n → M} {s : Set (Site n)} (h : LocalOn s f) (u : off b s) (Y : Config G n → G.Color) :
    coupled b Y f = 0 := by
  funext U; unfold coupled vary
  rw [show (fun v => f (tilt b U v)) = (fun _ => f U) from funext (isolated_outside b h u U)]
  simp
end YM.FormalOPE.RG10.InversionWard
