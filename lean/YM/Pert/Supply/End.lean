import YM.Pert.Flow.End
import YM.Pert.Supply.Base
import YM.Pert.Phases.Ranked

/-! Same Wilson extraction as `flowEndpoint` (retaining also the chart/scaling and partial quantitative laws there), now with supplies on the very same Family for `Bulk` conditional predictor bounds and the actual affine `Uncut` identity. These control the *deterministic* repeated-rank component once one has projection-null curvature packets; not claiming other marked-transfer terms are projection-null or match. -/
noncomputable section
namespace YM.Pert
open Function Filter Topology Extraction Flow Triangle Spec Maxwell Position Parity Scale
open scoped Topology
set_option maxHeartbeats 4000000 in
theorem budgetEndpoint (hg : G.Simple) {c:ℝ} (hc:0<c) :
    ∃ C : Family G,∃ B:PhysicalNext.RankCovariance.Binding C,C.path.levels.clock.kernel.penalty=c ∧ Extraction.Wcmain C ∧ MergeProof.Ribbons.Materials C ∧ MergeProof.Ribbons.Plenty C ∧
    ∀ f:Extraction.Order, ∃ (g:Extraction.Order) (S:Table C.book) (b:Final C (f.refine g) S) (X:Climb.Scaling S),
       FirstExtension b X ∧ Position.Crest X ∧ Triangle.TriangleBranch X ∧ RunningPort C (f.refine g) ∧
       ∃ (n:ℕ)(Q:Conditions C.labels 4 n) (φ : Ledger Q→Buffer C.labels 4) (J:Module.End ℝ (Fin n→ℝ)), CleanProfiles Q ∧ BoardAttains Q X φ ∧ Resident b X φ ∧ Parity.Fair Q J ∧ Parity.ParityFields φ ∧ Scale.Patch b X φ := by
     obtain ⟨C,B,hC,hW,hM,hP,H⟩ := Supply.combined hg hc
     refine ⟨C,B,hC,hW,hM,hP,fun f=>?_⟩
     obtain ⟨g,S,b,X,hX⟩ := H f
     have hR := credible b X hX
     obtain ⟨n,Q,J,hq,hJ,hClean⟩ := parity_four C hg
     obtain ⟨φ,hf⟩ := hR.position _ _ Q hClean hq
     exact ⟨g,S,b,X,hX,hR,attachTriangle hg hX,running_port hg hM.makes _,n,Q,φ,J,hClean,hf,residency b X hX hg hClean hf,hJ,fields_generator hJ hClean hf.toMode.patch,patch_ready hg hX hClean hf.toMode.patch⟩

end YM.Pert
