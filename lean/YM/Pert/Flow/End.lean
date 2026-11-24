import YM.Pert.Flow.Keep
import YM.Pert.Triangle.End
/-!
Partial scale-consumer and trajectory-step endpoint. `genuine` in this receipt is
the *bare/exact Wilson-path coefficient step*, uniformly along a cutoff tail,
NOT identification with the position diagnostic. `pick` interpolates it after
ordered extraction; `transfer` displays the necessary quantitative bend hypothesis.
`fixedColumnConsumer` addresses a remaining all-orders interface for field step
prices algebraically, on integer log inverse lengths; the hypothesis
`Layer.StepEstimate` (via `Orientations.rates`) must still be proved on actual
physical label comparisons, as must the moving-label array remainder itself.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Flow
open Function Filter Topology Extraction Asymptotics Price Layer Triangle
open Spec Maxwell Position Parity Scale
open scoped Topology
variable {G : Gauge} {C : Family G}
structure RunningPort (C : Family G) (F : Order) : Prop where
    genuine {N p : ℕ→ℕ} (hN : ∀ᶠ i:ℕ in atTop, i < N i) : Tendsto (fun i =>
         let g:= regulatorRun C (N i) (p i)
         ((g (i+1)-g i)/(g i)^3) / logStride C i) atTop (𝓝 (-b0 G))
    pick : Nonempty (Strain C F)
    signature P : Signature (b0 G) (proxy (G:=G) (C:=C) (F:=F) P)
    transfer P {y:ℝ→ℝ} {a b:ℝ} :
       Tendsto (Bent (proxy (G:=G) (C:=C) (F:=F) P) y a b) atTop (𝓝 0) → Signature (b0 G) y

lemma running_port (hG : G.Simple) (hc : C.Makes) (F:Order) : RunningPort C F :=
    ⟨fun h=>raw_beta_lead hc h hG, strain_exists hc F,proxySignature hG,fun P=>signedBend (proxySignature hG P)⟩

/-- Conditional fixed-label price lemma merging `qwil`/`qgr`-type normalization and inverse.
Arbitrary finite real bases of the same size (ordered by energy `e`), complex
array residuals, real positive-slope coupling. Offgrade costs and
polynomial bounds after the two engineering compensations; tensor remainders
on input/output transformations with fixed extra orders. -/
theorem fixedColumnConsumer {V I : Type*} [Fintype V] [Fintype I]
     {e : V → ℝ} {M A T U : TimeArray V} (h : Orientations e M A T U) {B} (hB : 0 < B) {u} (hU : Signature B u)
     (R : ℕ→Words ℂ V I)
     (hx : ∀ p:ℕ, ∀ j c, ∃ D≥(0:ℝ),∀ᶠ n in atTop, ‖R p n j c‖ ≤ D*|u n|^p) :
     let u' (n:ℕ):=u n
     (∀ j i:V,
      couplingTame u' (fun n=>normalizeCols M e n i j) ∧ couplingTame u' (fun n=>normalizeRows A e n j i)) ∧
     (∀ j i:V, e i < e j → couplingFlat u' (fun n=>normalizeCols M e n i j) ∧ couplingFlat u' (fun n=>normalizeRows A e n i j)) ∧
     ∀ j c (q:ℕ),∃ p:ℕ, p≥q ∧ ∃ D≥(0:ℝ), ∀ᶠ n:ℕ in atTop, ‖coupon e n j c • uponFields M A (R p) n j c‖ ≤ D*|u' n|^q :=
     ⟨couplingPrices h hB hU,fun _ _=>couplingLax h hB hU,fun _ _=>coupon_keep h R hB hU _ _ hx⟩

/-- Same-theory partial actual endpoint with `Triangle.triangleEndpoint` preserved. -/
theorem flowEndpoint (hg : G.Simple) {c:ℝ} (hc:0<c) :
    ∃ C : Family G,C.path.levels.clock.kernel.penalty=c ∧ Extraction.Wcmain C ∧ MergeProof.Ribbons.Materials C ∧ MergeProof.Ribbons.Plenty C ∧
    ∀ f:Extraction.Order, ∃ (g:Extraction.Order) (S:Table C.book) (b:Final C (f.refine g) S) (X:Climb.Scaling S),
       FirstExtension b X ∧ Position.Crest X ∧ Triangle.TriangleBranch X ∧ RunningPort C (f.refine g) ∧
       ∃ (n:ℕ)(Q:Conditions C.labels 4 n) (φ : Ledger Q→Buffer C.labels 4) (J:Module.End ℝ (Fin n→ℝ)), CleanProfiles Q ∧ BoardAttains Q X φ ∧ Resident b X φ ∧ Parity.Fair Q J ∧ Parity.ParityFields φ ∧ Scale.Patch b X φ := by
     obtain ⟨C,hC,hW,hM,hP,H⟩ := triangleEndpoint hg hc
     refine ⟨C,hC,hW,hM,hP,fun f=>?_⟩
     obtain ⟨g,S,b,X,hX,hC,hT,n,Q,φ,J,hClean,hA,hResident,hFair,hParityFields,hPatch⟩ := H f
     exact ⟨g,S,b,X,hX,hC,hT,running_port hg hM.makes _,n,Q,φ,J,hClean,hA,hResident,hFair,hParityFields,hPatch⟩
end YM.Pert.Flow
