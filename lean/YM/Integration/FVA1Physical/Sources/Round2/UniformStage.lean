import YM.Integration.FVA1Physical.Sources.Round2.OrderRecovery
import YM.Integration.FVA1Physical.Sources.Round2.CrossingBoxes

/-! Uniform physical error and the remaining forced boxes on an anchored
sector of one stage of a calibrated blocking window. -/

namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics

open MeasureTheory Lattice RG Wilson RG.Supply Input Org Source Extra.Histories LocalLTE LocalLTE.Sail
open ConnectedActivityE6 MergeProof MergeProof.Accent YM.Integration.FVA1Physical
open scoped BigOperators Classical

variable {G : Gauge} {X : Metals G} {R : Rolls X.p} {A : Alloy X R} {P : Bolt A}
variable {N n i : ℕ} {I : Type} [DecidableEq I] [Fintype I]
variable (B : Marker.Census I) (Y : Batch (Issue.trail P) N n I)
variable (π : ∀ j : ℕ, j ≤ N → Y.steering j)
variable (F : ∀ (j : I) (s : ℕ), ((Labels.frames G).level (Y.demand j)).Coeff →
  Coefficient ((Labels.frames G).level (Y.demand j)) ((Issue.trail P).S.side s n))
variable (hi : i < N) (O : Appendix B ((Issue.trail P).rep N n i))
variable (V : ∀ d, Music ((Labels.frames G).level d) (Issue.trail P) N n)

def uniformStage (D K W p : ℕ) : Prop :=
  let H := Issue.trail P
  let μ := prior G (H.S.side i n)
  let Z := Wilson.partition G (H.S.side N n) (H.β N n N)
  let δ := fun v => gasForecast B Y π F hi O V v - gust H N n N (Y.raw B) i hi.le v
  let ε := uniformGasCost G D K W p * Coat.gStep (H.rep N n (i + 1)).beta ^ (p + 1)
  (∀ v, Marker.Poly.price (fun _ => 1) (δ v) ≤ (H.rep N n i).eval v * ε) ∧
    ∀ (u : Config G (H.S.side i n) → B.Mode → ℂ), (∀ v j, ‖u v j‖ ≤ 1) →
      (∀ j, Measurable fun v => u v j) → ∀ e : Set (Config G (H.S.side i n)), MeasurableSet e →
      let f := fun v => modeTest (u v) (δ v)
      IntegrableOn f e μ ∧ (∫ v in e, ‖f v‖ ∂μ) / Z ≤ ε * (OPE.Therm.scene H N n i).real e

def crossingStage : Prop :=
  let H := Issue.trail P
  let Q := H.rep N n i
  ∀ (S : Support (H.S.side i n)) (v : Config G (H.S.side i n)),
    Healthy Q.p.threshold S v → gasForecast B Y π F hi O V v =
      (Real.exp (Q.exponent v) : ℂ) • (Marker.Poly.pass (Sail.forecast B O (spectralValue Y π F hi) v) *
        field (fun b => bar Q.activities B v b + if Sail.Round2.crossingBox (Y.origin i) S b then
          Mach B (fun j => profile Q.activities (Y.named V (π i hi.le) j).forced b v) + O.K b v else 0)
            (flags Q.p.threshold v))

theorem uniformStage_of_allFlags (hG : G.Simple) (hp : OPE.Therm.Poetry (Issue.trail P).levels)
    {D K W p : ℕ} (hw : N - (i + 1) ≤ W) (hd : ∀ j, Y.demand j ≤ D) (hk : Fintype.card I ≤ K)
    (hv : ∀ j, ((Labels.frames G).level (Y.demand j)).coeffSize (Y.voice j) ≤ 1)
    (h : allFlagStage B Y π F hi O V (upgradedOrder G D K p) K) :
    uniformStage B Y π F hi O V D K W p := by
  have hc := recoverPhysicalOrder hG hp hi W D K p hw Y hd hk hv
  constructor
  · intro v
    exact (h.1 v).trans (mul_le_mul_of_nonneg_left hc
      (SectorNext.Vacuum.strictly (Issue.trail P) P.choice N n i hi.le v).le)
  intro u hu hm e he
  obtain ⟨hf, hh⟩ := h.2 u hu hm e he
  exact ⟨hf, hh.trans (mul_le_mul_of_nonneg_right hc (ENNReal.toReal_nonneg))⟩

end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
