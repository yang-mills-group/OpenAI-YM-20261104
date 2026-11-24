import YM.Pert.Triangle.PositionBranch
/-!
The first-order interaction detector, bearing on a positional coupling choice.
Partial extension. `NonzeroTest` obtains a tested comparison-side continuum
first-order reading independent of the Wilson outputs, by the **reduced triangle**
formula. `TriangleBranch` puts the diagnostic on the weak-scaling frame of the
actual construction and by conditional position tests on the rolling relative
frames through six (no simultaneous order-one asymptotic matching assertion).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Pert.Triangle
open Function Maxwell Topology Set MeasureTheory Filter Position RawLabels Next Spec Climb Labels
open scoped Classical Topology ContDiff
variable {G:Gauge} (hg:G.Simple) (F:Frames G)
local notation "Ω" => Points 3

structure NonzeroTest (F : Frames G) : Prop where
    averaged (K : E4≃ₗᵢ[ℝ]E4) (x:Ω): profileChoice x = profileChoice (WithLp.toLp 2 (fun i:Fin 3=>K (x i)))
    separated : ∀ x∈tsupport profileChoice,farEnough x
    unscaledResponse : cTest G ≠ 0
    inert : profileChoice.applyTo (fun x=>(freeTable F).useAt (freeTable F) x (fun i:Fin 3=>Sigma.mk 6 (basic F i))) = 0
    detectorIndependent (D : Buffer F 6) (i:Fin 3) : let q:= update (basic F) i (D.1 (basic F i))
      profileChoice.applyTo (fun x=>(freeTable F).useAt (freeTable F) x (fun i=> Sigma.mk 6 (q i)))=0
include hg in
theorem finiteTest : NonzeroTest F := ⟨fun _ _=>(rotationFixed _ _).symm,(fun _=>choiceFar),diagnosticNonzero hg,?_,fun D i=>test_stability hg F D profileChoice i⟩
  where finally 
      apply Eq.trans (YM.Test.apply_eq profileChoice (P:=fun _=>0) (fun z hz=>free_point_base hg F hz))
      simp [Test.applyTo]

variable {C : Family G} {I:Extraction.Order} {S:Table C.book}
structure TriangleBranch (X:Scaling S) : Prop where
    diagnosis : NonzeroTest C.labels
    raw : Tendsto (bareMeasure X) atTop (𝓝 0)
    measuring (n) (Q:Conditions C.labels 6 n) (φ:Ledger Q → Buffer C.labels 6) (hq:CleanProfiles Q) (he:Reports (chart Q) (white Q) 0 φ) (t:ℝ) : 0<t → Tendsto (fun v : ℕ×ℝ => positionMeasure X Q (φ:=φ) v.1 v.2) (atTop ×ˢ𝓝 t) (𝓝 0)
include hg
lemma attachTriangle {X:Scaling S} {b:Final C I S} (h : FirstExtension b X) : TriangleBranch X :=
   ⟨finiteTest hg _, actual_bare_leading hg _ h, fun _ _ _ hQ hh _=>adjusted_limit hg _ h _ hQ hh⟩

/-- Unconditional existence with the shared witnesses of `scaleEndpoint`. Does *not*
assume all-order suppliers, nor conclude that first-order detector is the exact
PT regulator derivative. The current actual statements for the triangle are zeroth-order,
and on the cited scaling windows, with square position frame control only through four
(no assertion that the whole finite-horizon-6 frame here comes from an unconditional
square calibration). -/
theorem triangleEndpoint {c:ℝ} (hc:0<c) :
    ∃ C : Family G,C.path.levels.clock.kernel.penalty=c ∧ Extraction.Wcmain C ∧ MergeProof.Ribbons.Materials C ∧ MergeProof.Ribbons.Plenty C ∧
    ∀ f:Extraction.Order, ∃ (g:Extraction.Order) (S:Table C.book) (b:Final C (f.refine g) S) (X:Scaling S),
       FirstExtension b X ∧ Position.Crest X ∧ TriangleBranch X ∧ ∃ (n:ℕ)(Q:Conditions C.labels 4 n) (φ : Ledger Q→Buffer C.labels 4) (J:Module.End ℝ (Fin n→ℝ)), CleanProfiles Q ∧ BoardAttains Q X φ ∧ Resident b X φ ∧ Parity.Fair Q J ∧ Parity.ParityFields φ ∧ Scale.Patch b X φ := by
     obtain ⟨C,hC,hW,hM,hP,H⟩ := Scale.scaleEndpoint hg hc
     refine ⟨C,hC,hW,hM,hP,fun f=>?_⟩
     obtain ⟨g,S,b,X,hX,hU,n,Q,φ,J,hClean,hA,hResident,hFair,hParityFields,hPatch⟩ := H f
     exact ⟨g,S,b,X,hX,hU,attachTriangle hg hX,n,Q,φ,J,hClean,hA,hResident,hFair,hParityFields,hPatch⟩
end YM.Pert.Triangle
