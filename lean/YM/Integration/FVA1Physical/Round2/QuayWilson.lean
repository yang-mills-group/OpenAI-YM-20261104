import YM.Integration.FVA1Physical.Round2.QuayDictionary
import YM.Integration.FVA1Physical.Round2.PhysicalTestBank

/-! All joint centered Quay insertions are compared to the independent
Wilson recursion along the same measured non-bare history, including each
nonflat ray and each finite order. The constant can depend on the shape
of this history, and it is chosen before the complex stencil vectors. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Quay
open Function Finset Lattice RG YM.Wilson Tree Precision Source Labels Extra.Histories Marker
open LocalLTE.Sail PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Org RG.Supply
open MergeProof.Accent Bandage.Harmonics Next.Foundations FVA2.CityHistory
open Comparison.RG02 RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.WilsonXLocal
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge PertExtension PertExtension.Chart
open Integration.FVA1Physical.Wilson PertExtension.Series.Tested
open scoped Classical BigOperators
theorem quay_wilson_price {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D}
    (P : Bolt A) {I : Type} [DecidableEq I] [Fintype I] {N n i : ℕ} (B : Census I) (h : I→ℕ)
    (ref : ℕ→ℕ) (Y : ∀ d j t,TransferData ((Labels.frames G).level d) (Issue.trail P) j t)
    (T : Slices (Issue.trail P).levels n) (hi : i ≤ N) (room : (traversal T hi).Room G)
    (tag : (traversal T hi).Tags) (u : Pins G ((Issue.trail P).S.side i n))
    {Z : ChartRatio G} (s : B.Mode) (L : ℂ →L[ℝ] ℝ)
    (ok : YM.Family.Makes (YM.Family.mk (Issue.trail P)
      (Next.Foundations.hol G) (Labels.frames G) (Next.Foundations.localSection G) ref Y))
    (hZ : LocalRatio Z) (r : ℕ) :
    let H := Issue.trail P
    let C := YM.Family.mk H (Next.Foundations.hol G) (Labels.frames G) (Next.Foundations.localSection G) ref Y
    let a := actualOffset C n N i
    let g₀ := Pert.Asymptotics.regulatorRun C N n N
    ∃ K:ℝ,0≤K ∧ ∀ (v:∀ j,((frames G).level (h j)).Coeff),
      (∀ j,((frames G).level (h j)).coeffSize (v j)≤1) →
      let E := scalarWilsonBank (traversal T hi) room tag u a Z
        (L ∘ fullProduct (centeredBatch P N n h v).wavelengths s.val)
      let U := expLinks G _ (g₀ • u)
      let Q := ((((H).rep N n i).eval U:ℂ)⁻¹) • Bandage.Harmonics.vista (P:=P) (N:=N) (n:=n) B h v i hi U
      ‖L (Q.part s)-peval E r g₀‖ ≤ K*g₀^(r+1) := by
  intro H C a g₀
  let Y₀ : Batch H N n I := centeredBatch P N n h (fun _=>0)
  obtain ⟨K,hK,buy⟩ := physical_voice_price Y₀ s.val (traversal T hi) hZ room tag u a L r
  refine ⟨K,hK,?_⟩
  intro v hv E U Q
  let batch := centeredBatch P N n h v
  have live := (tested_batch B batch s L).1
  have pos := Local.RealStep.coupling_pos C N n N ok le_rfl
  have rate := (buy v hv).2 g₀ pos
  have compare : L (Q.part s) = (traversal T hi).conditioned (offset a g₀)
      (L ∘ fullProduct batch.wavelengths s.val) U := by
    change L ((((((H).rep N n i).eval U:ℂ)⁻¹) • Bandage.Harmonics.vista (P:=P) (N:=N) (n:=n) B h v i hi U).part s) = _
    rw [vista_moments, momentTable_descent B batch T hi P.choice s U, moment_part,line_offset ok]
    exact (measured L _ (room_ok _ room) live _).symm
  rw [compare]
  exact rate

end YM.Integration.FVA1Physical.Round2.Quay
