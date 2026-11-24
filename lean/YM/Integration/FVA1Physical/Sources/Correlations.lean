import YM.Integration.FVA1Physical.Sources.RepeatedReadout
import YM.Integration.FVA1Physical.Sources.TerminalMoment

/-! Reduce the full fine-lattice joint reading to its good-sector forecast and
the specific transported contribution on the complement. -/

namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics

open Function MeasureTheory Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open Extra.Histories Source Next.Foundations LocalLTE LocalLTE.Sail
open ConnectedActivityE6 MergeProof MergeProof.Accent YM.Integration.FVA1Physical
open scoped BigOperators

variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I]

omit [DecidableEq I] [Fintype I] in
theorem physicalField_continuous {H : History G} {N n : ℕ} (Y : Batch H N n I) (j : I) :
    Continuous (Y.wavelengths j) := by
  have he : Continuous (initial (localSection G (Y.demand j)) H N n (Y.voice j) 0) :=
    ((localSection G (Y.demand j)).continuous_places ..).const_smul _
  have hv := he.comp (continuous_pull (Y.motion j).1 (Y.origin N j))
  unfold Batch.wavelengths primProbe
  apply Continuous.const_smul
  unfold stepUp Motion.scalar
  dsimp only
  split
  · exact hv.star
  · exact hv

theorem physicalSeed_integrable (H : History G) (hH : H.Selected) {N n : ℕ}
    (B : Marker.Census I) (Y : Batch H N n I) :
    Integrable (Y.raw B) (prior G (H.S.side N n)) := by
  have hq : Continuous (H.rep N n N).eval := by
    rw [(hH.starts N n).2]
    exact bare_cont _
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  apply (Complex.continuous_ofReal.comp hq).smul
  apply Marker.Poly.pass_cont.comp
  refine continuous_finsetSum _ fun j _ => ?_
  change Continuous fun v => (Marker.Poly.send (B.fire j) (Y.wavelengths j v)).part
  apply continuous_pi
  intro m
  simp only [Marker.Poly.part_send]
  split_ifs
  · exact physicalField_continuous Y j
  · exact continuous_const

variable {X : Metals G} {D : Rolls X.p} {A : Alloy X D} {P : Bolt A} {N n i : ℕ}
variable (B : Marker.Census I) (Y : Batch (Issue.trail P) N n I)
variable (π : ∀ j : ℕ, j ≤ N → Y.steering j)
variable (fields : ∀ (j : I) (s : ℕ), ((Labels.frames G).level (Y.demand j)).Coeff →
  Coefficient ((Labels.frames G).level (Y.demand j)) ((Issue.trail P).S.side s n))
variable (hi : i < N) (O : Appendix B ((Issue.trail P).rep N n i))

/-- The one remaining flagged integral is part of the actual theory. Its
magnitude is not assumed small. The test on the terminal joint field is fixed
before any blocking step. -/
def physicalTerminalStage (p K : ℕ) : Prop :=
  let H := Issue.trail P
  let Q := H.rep N n i
  let Q' := H.rep N n (i+1)
  let q := (A.B.a.clock.op i n).push Q'.beta Q'.eval
  let actual := gust H N n N (Y.raw B) i hi.le
  let forecasted := fun v => Marker.Poly.pass (Sail.forecast B O (spectralValue Y π fields hi) v)
  let good := {v : Config G (H.S.side i n) | flags Q.p.threshold v = ∅}
  let μ := prior G (H.S.side i n)
  let Z := Wilson.partition G (H.S.side N n) (H.β N n N)
  ∀ u : B.Mode → ℂ, (∀ j, ‖u j‖ ≤ 1) →
    ‖((∫ v, modeTest u (Y.raw B v) ∂prior G (H.S.side N n)) -
        (∫ v in goodᶜ, modeTest u (actual v) ∂μ) -
        (∫ v in good, modeTest u (q v • forecasted v) ∂μ)) / (Z : ℂ)‖ ≤
      (Sail.margin K * 2) * Coat.gStep Q'.beta ^ ((p : ℝ) + 1)

theorem physicalTerminalStage_of_readout {p K : ℕ}
    (h : physicalTestedStage B Y π fields hi O p K) :
    physicalTerminalStage B Y π fields hi O p K := by
  let H := Issue.trail P
  let Q := H.rep N n i
  let Q' := H.rep N n (i+1)
  let q := (A.B.a.clock.op i n).push Q'.beta Q'.eval
  let raw := gust H N n N (Y.raw B) i hi.le
  let predicted := fun v => Marker.Poly.pass (Sail.forecast B O (spectralValue Y π fields hi) v)
  let good := {v : Config G (H.S.side i n) | flags Q.p.threshold v = ∅}
  let μ := prior G (H.S.side i n)
  have seed := physicalSeed_integrable H P.choice B Y
  intro u hu
  let L := modeFunctional u
  let actual := fun v => modeTest u (raw v)
  let forecast := fun v => modeTest u (q v • predicted v)
  have hact : Integrable actual μ := L.integrable_comp (gust_live H N n N (Y.raw B) seed hi.le)
  have hdiff : (fun v => modeTest u (raw v - q v • predicted v)) =
      (fun v => actual v - forecast v) := funext fun v => L.map_sub _ _
  obtain ⟨_, hmeas, hnorm⟩ := h (fun _ => u) (fun _ j => hu j)
  obtain ⟨hgood, _⟩ := hmeas (fun _ => measurable_const)
  rw [hdiff] at hgood hnorm
  rw [← terminal_modeTest_conservation H N n i hi.le (Y.raw B) seed u]
  exact readout_away_from_exception μ (flags_measurable_eq _ _) actual forecast
    hact hgood _ _ hnorm

end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
