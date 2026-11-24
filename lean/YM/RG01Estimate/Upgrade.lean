import YM.RG01Estimate.AwardPath
import YM.UVExtension.Reports.Ultraviolet
/-! # Single actual provider with additional Calendar hooks. Use THIS strengthening
 before choosing a family. Don't replace a witness after calibrating. Penalty same.
 `Grant` buys before UV construction. Includes SAME output shapes as comparison_UV theorem.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Chart
open UVExtension Reports
open RG Lattice MeasureTheory Function Filter Extraction Spec Wilson Push
open Topology Precision PhysicalNext PhysicalNext.Repeat Legato Org Input
open Next.UVStress
open scoped Topology BigOperators Classical ContDiff

-- simultaneous (and preserve every-phase applying to selecting F AFTER)
theorem upgrade (G:Gauge)(h:G.Simple) (penalty:ℝ)(hp:0<penalty) {goal:Goal G}(hg:Funds goal):
    ∃ (C : Family G) (f: Extraction.Order) (T:Table C.book),
      Nonempty (Final C f T) ∧ C.Makes ∧ Spec.Calibrated C ∧
        C.path.levels.clock.kernel.penalty=penalty ∧
        Oasis.Floral (hG:=h) C ∧
        (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T ∧
        (∀ d k:ℕ,∀ᶠ n in atTop,
          ∀ (r:ℕ) (v:Fin r→ C.book.Token), (∀ i,(v i).1≤d) →
            ∃ g,Poppy.Margins C r n k v g) ∧ Award h goal C := by
    obtain ⟨C,hB,hC,hM,hW,hE,H,hQ,hF⟩:= fullClock h hp hg
    obtain ⟨g,A,L,R,T,E,hA,s,hN⟩:= hF Extraction.Order.full
    obtain ⟨hs,hG⟩:= hQ (Extraction.Order.full.refine g) s.copies
    obtain ⟨M,I,hI,p⟩:= YM.MergeProof.Acme.emanate (W:=E) H h hs hG s hA.clean.ready hA.clean.tilt
    have hx:= YM.MergeProof.Acme.glistens hC hA.clean.ready hA.clean.tilt p
    have he:= hE.floral h
    exact ⟨C,_,T,hx,hM,hC,hB,he,useFull he hx,Poppy.bravo (Oasis.appears he),hE⟩
end YM.RG01Estimate.Chart
