import YM.Integration.LocalComparisonPackets
import YM.Integration.ActualQlocalSignedTransport

/-!
Minimal output vocabulary for the full manuscript local theorem. All fields
below belong to one produced output; they are not assumptions on its input.
The full target supplies the prescribed coefficients, canonical reclosure,
aligned rows and quantitative estimates on these same objects separately.
In particular the formal density identity does not assert canonicality or
identify the formal regular log with an unmasked packet on bad fields.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal
open Function MeasureTheory Lattice Wilson RG Marker MergeProof MergeProof.Accent
open Extra.Trajectories OPE.Therm LocalComparison
open RG3.Script.Picnic
open scoped Classical BigOperators

variable {G : Gauge}

/-- A physical carrier fixes the native path, clipping and norm. Its full
vacuum is not assumed to equal the fixed trajectory vacuum. -/
structure PhysicalCarrier (C : Family G) (N period level : ℕ) where
  rep : Rep G (C.side level period)
  path : rep.path = (C.path.rep N period level).path
  clip : rep.clip = (C.path.rep N period level).clip
  point : rep.p = C.path.levels.budget level

/-- Attach the actual vacuum only when its complete value is identified. -/
def PhysicalCarrier.onActual {C : Family G} {N period level : ℕ}
    (Q : PhysicalCarrier C N period level)
    (h : Q.rep.eval = (C.path.rep N period level).eval) :
    Carrier C N period level :=
  ⟨Q.rep, Q.path, Q.clip, Q.point, h⟩

variable {C : Family G} {V : Type} [Fintype V] [DecidableEq V] {R : Census V}

/-- One complete output chosen by the local theorem. `output` is its aligned
actual representation. The formal companion and residual use the very same
carrier and roots. Canonical reclosure and common row supports are additional
conclusions of the full theorem, not consequences of a density equality. -/
structure ProducedOutput {N period level : ℕ}
    (D : V → ComparisonDensity.Address.Orbit)
    (fine : PhysicalCarrier C N period (level + 1))
    (fineRoots : V → Site (C.side (level + 1) period))
    (coarseRoots : V → Site (C.side level period))
    (input : Taste (TestSpace D) fineRoots fine.rep R) where
  carrier : PhysicalCarrier C N period level
  model : MarkedPackets D G (C.side level period) R
  output : Taste (TestSpace D) coarseRoots carrier.rep R
  residual : Taste (TestSpace D) coarseRoots carrier.rep R
  formalAligned : Taste (TestSpace D) coarseRoots carrier.rep R
  roots v : (C.path.levels.clock.op level period).ratio.parent (fineRoots v) =
    coarseRoots v
  vacuum : (C.path.levels.clock.op level period).push
    (C.path.β N period (level + 1)) fine.rep.eval = carrier.rep.eval
  density x : actualPush C N period level ((input.leaf x).density) =
    (output.leaf x).density
  full x U : (output.leaf x).density U =
    Poly.pass (model.read x (Pert.Asymptotics.regulatorRun C N period (level + 1)) U) *
      (residual.leaf x).density U
  formal_full x U : (formalAligned.leaf x).density U = carrier.rep.eval U •
    Poly.pass (model.read x (Pert.Asymptotics.regulatorRun C N period (level + 1)) U)
  regular_log x U : (output.leaf x).log U =
    (formalAligned.leaf x).log U + (residual.leaf x).log U

namespace ProducedOutput
variable {D : V → ComparisonDensity.Address.Orbit} {N p m : ℕ}
    {Q : PhysicalCarrier C N p (m + 1)}
    {o : V → Site (C.side (m + 1) p)} {o' : V → Site (C.side m p)}
    {input : Taste (TestSpace D) o Q.rep R} (O : ProducedOutput D Q o o' input)

/-- The complete chosen packet model, including every completion term. -/
def modelValue (x : TestSpace D) (U : Config G (C.side m p)) : Poly R :=
  Poly.pass (O.model.read x (Pert.Asymptotics.regulatorRun C N p (m + 1)) U)

/-- The full normalized residual, retaining its regular and forced parts. -/
def residualError (x : TestSpace D) (U : Config G (C.side m p)) : Poly R :=
  ((C.path.rep N p m).eval U)⁻¹ • (O.residual.leaf x).density U - 1

/-- The actual coarse vacuum follows from the full scalar transition. -/
theorem output_vacuum (hC : C.Makes) (hm : m < N)
    (hFine : Q.rep.eval = (C.path.rep N p (m + 1)).eval) :
    O.carrier.rep.eval = (C.path.rep N p m).eval := by
  calc
    O.carrier.rep.eval = (C.path.levels.clock.op m p).push
        (C.path.β N p (m + 1)) Q.rep.eval := O.vacuum.symm
    _ = (C.path.levels.clock.op m p).push (C.path.β N p (m + 1))
        (C.path.rep N p (m + 1)).eval := congrArg _ hFine
    _ = (C.path.rep N p m).eval := (hC.wilson.steps N p m hm).1.symm

/-- The produced scalar and marked data instantiate the native exact step. -/
theorem exact_step (hC : C.Makes) (hm : m < N)
    (hFine : Q.rep.eval = (C.path.rep N p (m + 1)).eval) :
    ExactStep (Q.onActual hFine)
      (O.carrier.onActual (O.output_vacuum hC hm hFine)) o o' input O.output where
  roots := O.roots
  density := O.density

/-- The complete output is the original numerator divided by original P0. -/
theorem normalized_output (hC : C.Makes)
    (hFine : Q.rep.eval = (C.path.rep N p (m + 1)).eval)
    {j : ℕ} (hj : j ≤ N) (hm : m < j)
    (source : TestSpace D → Config G (C.side j p) → Poly R)
    (hInput : ∀ x, (input.leaf x).density =
      gust C.path N p j (source x) (m + 1) hm)
    (x : TestSpace D) (U : Config G (C.side m p)) :
    actualSignedTransport C (N := N) (source x) hm.le U =
      ((C.path.rep N p m).eval U)⁻¹ • (O.output.leaf x).density U := by
  have h := ActualQlocalSignedTransport.normalized_output
    (O.exact_step hC (hm.trans_le hj) hFine) hC hj hm source hInput x U
  change actualSignedTransport C (N := N) (source x) hm.le U =
    (O.carrier.rep.eval U)⁻¹ • (O.output.leaf x).density U at h
  simpa only [O.output_vacuum hC (hm.trans_le hj) hFine] using h

/-- The additive error keeps the entire chosen model multiplier. -/
theorem additive_defect (hC : C.Makes)
    (hFine : Q.rep.eval = (C.path.rep N p (m + 1)).eval)
    {j : ℕ} (hj : j ≤ N) (hm : m < j)
    (source : TestSpace D → Config G (C.side j p) → Poly R)
    (hInput : ∀ x, (input.leaf x).density =
      gust C.path N p j (source x) (m + 1) hm)
    (x : TestSpace D) (U : Config G (C.side m p)) :
    actualSignedTransport C (N := N) (source x) hm.le U - O.modelValue x U =
      O.modelValue x U * O.residualError x U := by
  have h := ActualQlocalSignedTransport.additive_defect
    (O.exact_step hC (hm.trans_le hj) hFine) hC hj hm source hInput
    O.residual O.modelValue O.full x U
  change actualSignedTransport C (N := N) (source x) hm.le U - O.modelValue x U =
    O.modelValue x U * ((O.carrier.rep.eval U)⁻¹ • (O.residual.leaf x).density U - 1) at h
  simpa only [residualError, O.output_vacuum hC (hm.trans_le hj) hFine] using h

/-- Signed linear compression is applied after the full model-residual product.
Any remaining model-versus-candidate discrepancy is retained. -/
theorem linear_comparison {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hC : C.Makes) (hFine : Q.rep.eval = (C.path.rep N p (m + 1)).eval)
    {j : ℕ} (hj : j ≤ N) (hm : m < j)
    (source : TestSpace D → Config G (C.side j p) → Poly R)
    (hInput : ∀ x, (input.leaf x).density =
      gust C.path N p j (source x) (m + 1) hm)
    (L : Poly R →L[ℝ] E) (candidate : TestSpace D → Config G (C.side m p) → E)
    (x : TestSpace D) (U : Config G (C.side m p)) :
    L (actualSignedTransport C (N := N) (source x) hm.le U) - candidate x U =
      L (O.modelValue x U * O.residualError x U) +
        (L (O.modelValue x U) - candidate x U) := by
  have h := congrArg L (O.additive_defect hC hFine hj hm source hInput x U)
  rw [map_sub] at h
  rw [← h]
  abel

/-- The exact local identity consumed by the finite transport telescope. -/
theorem model_step_defect (hC : C.Makes) (hm : m < N)
    (hFine : Q.rep.eval = (C.path.rep N p (m + 1)).eval)
    (fineModel : TestSpace D → Config G (C.side (m + 1) p) → Poly R)
    (hInput : ∀ x, (input.leaf x).density = fun U => Q.rep.eval U • fineModel x U)
    (x : TestSpace D) (U : Config G (C.side m p)) :
    actualTransport C (N := N) (fineModel x) (Nat.le_succ m) U - O.modelValue x U =
      O.modelValue x U * O.residualError x U := by
  have h := ActualQlocalSignedTransport.model_step_defect
    (O.exact_step hC hm hFine) hC hm fineModel hInput O.residual O.modelValue O.full x U
  change actualTransport C (N := N) (fineModel x) (Nat.le_succ m) U - O.modelValue x U =
    O.modelValue x U * ((O.carrier.rep.eval U)⁻¹ • (O.residual.leaf x).density U - 1) at h
  simpa only [residualError, O.output_vacuum hC hm hFine] using h

end ProducedOutput
end YM.Integration.FullQLocal
end
