import YM.Trace.Physicalv2.GermChain
import YM.Integration.FullQLocalProducedOutput
import YM.Integration.LocalComparisonSignedRemainder

/-! Extraction of the exact signed one-mark transmission from the full marked
Wilson step. Both terms are read from the selected coarse representation.
The physical transfer includes the engineering factor of the one-mark graph. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.Integration.ActualQLocalGraphDefect

open Filter MeasureTheory Lattice Wilson RG Marker
open Extra.Histories Extra.Trajectories MergeProof MergeProof.Accent
open Trace.Physical Trace.Physical.GermGraph LocalComparison FullQLocal
open RG3.Script.Picnic
open scoped Topology Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {I : Type} [Fintype I] [DecidableEq I]
    {Γ : Census I} {D : I → ComparisonDensity.Address.Orbit} {N p i : ℕ}
    {Q : PhysicalCarrier C N p (i+1)}
    {o : I → Site (C.side (i+1) p)} {o' : I → Site (C.side i p)}
    {input : Taste (TestSpace D) o Q.rep Γ}
    (O : ProducedOutput D Q o o' input) (H : C.Makes) (hi : i<N)
    (hf : Q.rep.eval = (C.path.rep N p (i+1)).eval)
    (x : TestSpace D)
    (hint : Integrable (input.leaf x).density (prior G _))
    (hquiet : ∀ U, ((input.leaf x).density U).part Γ.quiet =
      ((C.path.rep N p (i+1)).eval U : ℂ))

include H hi hf hint hquiet in
theorem residual_quiet (U : Config G (C.side i p)) :
    ((O.residual.leaf x).density U).part Γ.quiet = (O.carrier.rep.eval U : ℂ) := by
  have hc := actualPush_quiet H hi (input.leaf x).density hint hquiet U
  rw [O.density x, O.full x U, Poly.quiet_mul,
    Poly.pass_part _ (O.model.quiet_read x _ U), one_mul] at hc
  rw [O.output_vacuum H hi hf]
  exact hc

include H hi hf hint hquiet in
/-- The actual integral supplies the quiet coefficient. Extracting the
singleton of the product therefore preserves the two full signed densities. -/
theorem singleton (j : I) (d : ℕ) :
    transition (C := C) d N p i (fun W => ((input.leaf x).density W).part (Γ.fire j)) =
      ((C.S.block i).val : ℂ)^d •
        (fun W => ((O.formalAligned.leaf x).density W).part (Γ.fire j)) +
      ((C.S.block i).val : ℂ)^d •
        (fun W => ((O.residual.leaf x).density W).part (Γ.fire j)) := by
  have hp : (fun W => ((O.output.leaf x).density W).part (Γ.fire j)) =
      (C.path.levels.clock.op i p).push (C.path.β N p (i+1))
        (fun W => ((input.leaf x).density W).part (Γ.fire j)) := by
    rw [← O.density x]
    exact push_get (C.path.levels.transition_mass i p _) hint (Γ.fire j)
  rw [transition, blast, ← hp, ← smul_add]
  congr 1
  funext W
  change ((O.output.leaf x).density W).part (Γ.fire j) =
    ((O.formalAligned.leaf x).density W).part (Γ.fire j) +
    ((O.residual.leaf x).density W).part (Γ.fire j)
  rw [O.full x W, O.formal_full x W, shock Γ,
    Poly.pass_part _ (O.model.quiet_read x _ W), one_mul,
    residual_quiet O H hi hf x hint hquiet W]
  let a := (O.model.read x (Pert.Asymptotics.regulatorRun C N p (i+1)) W).pass.part (Γ.fire j)
  let e := ((O.residual.leaf x).density W).part (Γ.fire j)
  let z := (O.carrier.rep.eval W : ℂ)
  change e + a*z = z*a + e
  rw [mul_comm a z, add_comm]

include H hi hf hint hquiet in
/-- With the supplied formal singleton and signed residual represented in
the native graph frame, the local signed-defect identity follows from the
selected physical output. All three realizations concern this same test. -/
theorem represented (j : I) (d : ℕ) {fine : GermGraph.store C d p (i+1)}
    {main e : GermGraph.store C d p i}
    (hin : value d N p (i+1) fine =
      fun W => ((input.leaf x).density W).part (Γ.fire j))
    (hout : value d N p i main = ((C.S.block i).val : ℂ)^d •
      (fun W => ((O.formalAligned.leaf x).density W).part (Γ.fire j)))
    (herr : value d N p i e = ((C.S.block i).val : ℂ)^d •
      (fun W => ((O.residual.leaf x).density W).part (Γ.fire j))) :
    transition (C := C) d N p i (value d N p (i+1) fine) =
      value d N p i main + value d N p i e := by
  rw [hin, hout, herr]
  exact singleton O H hi hf x hint hquiet j d

include H hi hf hint hquiet in
/-- The complete represented cost required by the native stable-graph
theorem, obtained from the residual in the selected full polynomial. -/
theorem foreground (j : I) (d : ℕ) {fine : GermGraph.store C d p (i+1)}
    {main e : GermGraph.store C d p i} {b : ℝ}
    (hin : value d N p (i+1) fine =
      fun W => ((input.leaf x).density W).part (Γ.fire j))
    (hout : value d N p i main = ((C.S.block i).val : ℂ)^d •
      (fun W => ((O.formalAligned.leaf x).density W).part (Γ.fire j)))
    (herr : value d N p i e = ((C.S.block i).val : ℂ)^d •
      (fun W => ((O.residual.leaf x).density W).part (Γ.fire j)))
    (he : reads d N p i e b) (hcoord : (C.labels.level d).coeffSize e.x ≤ b) :
    Foreground C d N p i
      (transition (C := C) d N p i (value d N p (i+1) fine) - value d N p i main)
      ((1+4*stock C i)*b) := by
  refine ⟨b, e, (Work.G08.size_nonneg _ _).trans hcoord, he, hcoord, ?_, le_rfl⟩
  rw [represented O H hi hf x hint hquiet j d hin hout herr]
  abel

end YM.Integration.ActualQLocalGraphDefect
end
