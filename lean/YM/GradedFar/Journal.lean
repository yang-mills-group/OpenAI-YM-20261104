import YM.GradedFar.Indices
import YM.FullVolume.Profiles
/-!
# Source of the actual full mesh purchase

Use full `PositionsUV` (separate hypothesis). Same F. Assert *successive* limits as text:
smears full-UV then period subsequence (our statement `towards` also has eventual validity of period-parameter
suitable etc on that order); point comparison along cover & paired tails even varying positions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Auth
open Function Filter Set PowerSeries MeasureTheory Lattice RG Wilson Extraction Extraction.Lease Spec
open Metric FullVolume
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book} (F:Final C f S)

-- cf FullVolume/Finale/Program (could reuse in application)
lemma journals (h:PositionsUV C Extraction.Sequence.full): ClusterFrames C:= by
 intro p n w; obtain ⟨f,_,_,H⟩:= h p n w; exact ⟨f,(H []).1⟩
include F
lemma towards (h:PositionsUV C Extraction.Sequence.full): (again f).Ordered C S:=by
 refine ⟨ fun n v t=>?_⟩; obtain ⟨ht,D,hD,hV⟩ := F.room.ordered.reads n v t; refine ⟨ht,D,fun p h' => ?_,hV⟩
 obtain ⟨g,hg,h₁,_⟩:= h p n v; have hx:= h₁ t h'; exact tendsto_nhds_unique (hx.comp f.mesh.cofinal) (hD p h') ▸ hx
variable {n:ℕ}
lemma both_pulses (hF:FixedBounds C) (h:PositionsUV C Extraction.Sequence.full) (v:Fin n→ C.book.Token):∃ L:ℕ→Points n→ℂ,
    (∀ p:ℕ, Cluster C Extraction.Sequence.full p n (fun N=>lifted C N p v) (L p) ∧
      ∀ t:Test n, suitable C.S p t→ Tendsto (fun j=>Order.smears C j p v t) atTop (𝓝 (t.applyTo (L p)))) ∧
    ∀ K:Set (Points n), IsCompact K→ K⊆ conf n→ ∀ ε:ℝ,0<ε→ ∀ᶠ i:ℕ in atTop,∀ x∈K, dist (L (f.per i) x) (S.read x v)≤ε:= by
 choose L hc h₁ H using fun p=> h p n v; refine ⟨L,fun i=>⟨?_,h₁ i⟩, fun K hK hx ε he=> many F hF (fun p=> ?_) hK hx ε he⟩
 exacts [(H i []).1,(H p []).1]
end YM.Integration.GradedFar.Auth
