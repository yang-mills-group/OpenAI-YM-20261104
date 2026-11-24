import YM.OPE.Levy.Phase
import YM.OPE.Short.Partial

/-!
# One OPE hierarchy linked to a weak X-space/graded-column extraction

One-sided engineering amplification rates along the very same frames
used for one actual `FirstExtension`. Includes estimates on projection
remnants in previously separated inputs (cf. `Levy.residual_rate` for
moving placements) and the every-character separated leading
identity-channel prediction (`testedZero` = `Short.scalar`, unit
coefficient of the exact OPE; evaluated with measured input labels).

No log replacement for general inverse normalizations or all ratios from
this theorem; the costs in both reciprocal spacings are still o(main
spatial exponential rate), not automatically powers of log or powers of
running coupling. There is no full X-space matching hypothesis instantiated
as if already supplied here. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.OPE.Levy
open Filter Set Function Table Ward Orbits Extraction Climb Next.UVStress Spec Pert Nesting
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}

structure Ticket (U:Final C F S)(R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (X:Scaling S):Prop where
  comparison : FirstExtension U X
  slopes : Anchored U.sector.derivatives (path X) (isoPanel X)
  inverse(d:ℕ)(v:S.Field d): RateLE atTop (zstamp (path X)) (fun i=>(X.U i d).symm v) (d:ℝ)
  prediction(I:Type)[Fintype I](b:I→ℕ)(v:∀i,(Bel C.book).Field (b i))(M η:ℝ): 0 < η → ∀ ε > (0:ℝ), ∀ᶠ k in atTop,∀ x∈Short.plate I M η, ∀ (o:E4)(q:Viewers U), ‖testedZero U R X v k x o-freeSlots v x‖ ≤ ε ∧ ‖testedWord U X v k x o q-freeSlots v x‖ ≤ ε

variable (U:Final C F S)(R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (X:Scaling S) (H:Anchored U.sector.derivatives (path X) (isoPanel X)) (h₀:Services C F S)
include H h₀ in
lemma tickets (hX:FirstExtension U X): Ticket U R X := by
    constructor
    · exact hX
    · exact H
    · exact fun d v=>inverse_subpower U d X hX h₀ v
    exact fun I _ b v M η he ε hε => consistent U R X H h₀ v he h₀.simpleGate hX _ hε

/-- Strengthen the auxiliary complete-weak comparison of
OPE.Rough.Supply/Measuring.Joined as well as `Base` inputs, before choosing
a single hierarchy. -/
theorem integrated (G:Gauge)(hG : G.Simple) (κ:ℝ)(hκ:0 < κ) :∃ (C:Family G),C.path.levels.clock.kernel.penalty=κ ∧ Wcmain C ∧ ∀ (F:Order), ∃(f:Extraction.Order) (S:Table C.book), Services C (F.refine f) S ∧ ∃ (U:Spec.Final C (F.refine f) S) (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin) (X:Scaling S), Sparse.Quiet U R ∧ Nesting.Uniform U R ∧ Foundation U R ∧ Ticket U R X ∧ Short.Partial U R X ∧ Approaches (Next.UVStress.path X) (Next.UVStress.isoPanel X) := by
   obtain ⟨C,hV,hW,h⟩:=simultaneous G hG κ hκ
   refine ⟨C,hV,hW,fun F=>?_⟩
   obtain ⟨f,S,h,U,R,X,h₁,h₂,h₃,h₄,ha⟩:=h F
   exact ⟨f,S,h,U,R,X,Sparse.quiet U R h,h₂,h₄,tickets U R X h₃ h h₁,Short.wave U R X h₁ h,ha⟩
end YM.OPE.Levy
