import YM.Integration.FVA1Physical.Marked.MicroscopicField
import YM.Integration.FVA1Physical.Wilson.VaryingPhysical

/-! All microscopic C18 physical insertion batches have analytic chart
germs, including arbitrary complex test coefficients, orientation and
conjugate motion. No choice of presentation or gauge averaging changes
the field on configurations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Function MeasureTheory Lattice RG YM.Wilson Tree Precision
open LocalLTE.Sail Source Labels Extra.Histories MergeProof Next.Foundations Marker Comparison.RG02
open RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.Spool
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open FVA2.CityHistory FormalOPE.RG10 PhysicalNext.Repeat.Legato
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d} (P : SectionData F)

private theorem entry_analytic (o : Site n) (i : Index G P.stencil) :
    ContDiffAt ℝ ω (fun v : Pins G n => entry (expandAt o (expLinks G _ v)) i) 0 := by
  let e : Edge (Site n) := (wrap n i.1.val.1 + o,i.1.val.2)
  let coord := Matrix.entryLinearMap ℝ ℂ i.2.1 i.2.2.1
  have z : ContDiffAt ℝ ω (fun v : Pins G n => G.mat (G.lieExp (v e)) i.2.1 i.2.2.1) 0 :=
    coord.toContinuousLinearMap.contDiff.contDiffAt.comp 0
      (G.exp_jet.contDiffAt.comp (f:=fun v : Pins G n => v e) 0 (contDiff_apply ℝ _ e).contDiffAt)
  unfold Source.entry
  split
  · exact (starL ℝ : ℂ ≃L[ℝ] ℂ).contDiff.contDiffAt.comp 0 z
  exact z

theorem chart_places (a : F.Coeff) (o : Site n) :
    ContDiffAt ℝ ω (P.places a o ∘ expLinks G (Edge (Site n))) 0 := by
  let U := fun v : Pins G n => expandAt o (expLinks G _ v)
  have H (Q : Source.Formula G P.stencil) : ContDiffAt ℝ ω (fun v => MvPolynomial.aeval (entry (U v)) Q) 0 := by
    induction Q using MvPolynomial.induction_on with
    | C c => simp_rw [MvPolynomial.aeval_C,Algebra.algebraMap_self_apply]; exact contDiffAt_const
    | add p q hp hq => simp_rw [map_add]; exact hp.add hq
    | mul_X p i hp => simp_rw [map_mul,MvPolynomial.aeval_X]; exact hp.mul (entry_analytic P o i)
  exact H (P.evalC a)

variable {I : Type} (H : History G) (N n₀ : ℕ) (Y : Batch H N n₀ I) (i : I)
private theorem signed_wavelength (V : Config G (H.S.side N n₀)) :
    let l := Y.demand i
    let M := Y.motion i
    let s := ((Labels.frames G).level l).scaled (H.levels.clock.threshold N)⁻¹ (Y.voice i)
    let a := (H.S.a N : ℂ)^l
    Y.wavelengths i V = a * Motion.scalar M (a⁻¹ * (localSection G l).places
      (((Labels.frames G).level l).act M.1.ortho s) (affine M.1 (Y.origin N i) 0) V) := by
  intro l M s a
  change a * Motion.scalar M (a⁻¹ * (localSection G l).places s 0 (pull M.1 (Y.origin N i) V)) = _
  rw [SectionData.placed_signed _ (sound G l)]

theorem wavelength_witnessed :
    Continuous (Y.wavelengths i) ∧ GaugeInvariant (Y.wavelengths i) ∧
      ContDiffAt ℝ ω (Y.wavelengths i ∘ expLinks G (Edge (Site (H.S.side N n₀)))) 0 := by
  let l := Y.demand i
  let M := Y.motion i
  let P := localSection G l
  let c := ((Labels.frames G).level l).act M.1.ortho
    (((Labels.frames G).level l).scaled (H.levels.clock.threshold N)⁻¹ (Y.voice i))
  let o := affine M.1 (Y.origin N i) 0
  let a := (H.S.a N : ℂ)^l
  have eqn : Y.wavelengths i = fun U => a * Motion.scalar M (a⁻¹ * P.places c o U) := funext (signed_wavelength H N n₀ Y i)
  rw [eqn]
  have cont : Continuous (fun x => a⁻¹ * P.places c o x) := continuous_const.mul (P.continuous_places c o)
  have hot : ContDiffAt ℝ ω (fun x => a⁻¹ * P.places c o (expLinks G _ x)) 0 :=
    contDiffAt_const.mul (chart_places P c o)
  constructor
  · unfold Motion.scalar; split
    · exact continuous_const.mul (continuous_star.comp cont)
    exact continuous_const.mul cont
  constructor
  · intro k U; exact congrArg (fun z => a * Motion.scalar M (a⁻¹ * z)) (P.placed_invariant (sound G l) o c k U)
  unfold Motion.scalar; split
  · exact contDiffAt_const.mul ((starL ℝ : ℂ ≃L[ℝ] ℂ).contDiff.contDiffAt.comp 0 hot)
  exact contDiffAt_const.mul hot

end YM.Integration.FVA1Physical.Wilson
