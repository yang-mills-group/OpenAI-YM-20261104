import YM.Integration.FVA1Physical.Round2.QuayWilson

/-! Compare the Quay retained forecast for a physical joint insertion to
the independent conditional Wilson recursion by evaluating both on the
same calibrated history and healthy coarse configuration. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Quay
open Function Finset Lattice RG YM.Wilson Tree Precision Source Labels Extra.Histories Marker
open LocalLTE.Sail PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Org RG.Supply
open MergeProof.Accent Bandage.Harmonics Next.Foundations FVA2.CityHistory UVNext.CouplingReset
open Comparison.RG02 RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.WilsonXLocal
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge PertExtension PertExtension.Chart
open Integration.FVA1Physical.Wilson PertExtension.Series.Tested
open scoped Classical BigOperators
theorem forecast_wilson {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D}
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
    let g₀ := Pert.Asymptotics.regulatorRun C N n N
    let U₀ := expLinks G _ (g₀ • u)
    let φ := if i=N then (H.rep N n N).beta else (H.rep N n (i+1)).beta
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (v : ∀ j, ((frames G).level (h j)).Coeff),
      (∀ j, ((frames G).level (h j)).coeffSize (v j) ≤ 1) →
      ∀ (κ A₀ : ℝ) (p p₀ d ξ τ : ℕ) (b f : Coefficient ((frames G).level d) ((H).S.side i n)),
      Booklet (P:=P) B h v i hi κ p p₀ A₀ s d b f ξ τ →
      flags ((H).rep N n i).p.threshold U₀ = ∅ →
      let E := scalarWilsonBank (traversal T hi) room tag u (actualOffset C n N i) Z
        (L ∘ fullProduct (centeredBatch P N n h v).wavelengths s.val)
      ‖L (f.exponentialEntry 0 (localSection G d) ((H).rep N n i) U₀)-peval E r g₀‖ ≤
        ‖L‖ * PhysicalNext.Repeat.Legato.Spool.powerR p φ + K*g₀^(r+1) := by
  intro H C g₀ U₀ φ
  obtain ⟨K,hK,buy⟩ := quay_wilson_price P B h ref Y T hi room tag u s L ok hZ r
  refine ⟨K,hK,?_⟩
  intro v unit κ A₀ p p₀ d ξ τ b f hb healthy E
  let y := ((((H).rep N n i).eval U₀ : ℂ)⁻¹) • Bandage.Harmonics.vista (P:=P) (N:=N) (n:=n) B h v i hi U₀
  let z := f.exponentialEntry 0 (localSection G d) ((H).rep N n i) U₀
  have read := (hb.reads U₀ healthy).2.2
  have real_part (a : ℝ) (x : Poly B) : (a • x).part s = (a : ℂ) * x.part s := rfl
  have dist : ‖y.part s-z‖ ≤ PhysicalNext.Repeat.Legato.Spool.powerR p φ := by
    simpa only [y,z,φ,H,Poly.part_smul,real_part,Complex.ofReal_inv] using read
  have e : ‖L (y.part s)-peval E r g₀‖ ≤ K*g₀^(r+1) := buy v unit
  have move : ‖L z - L (y.part s)‖ ≤ ‖L‖*PhysicalNext.Repeat.Legato.Spool.powerR p φ := by
    rw [← L.map_sub]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((norm_sub_rev z (y.part s)).le.trans dist)
      (norm_nonneg _))
  have tri := dist_triangle (L z) (L (y.part s)) (peval E r g₀)
  rw [dist_eq_norm,dist_eq_norm,dist_eq_norm] at tri
  exact tri.trans (add_le_add move e)

end YM.Integration.FVA1Physical.Round2.Quay
