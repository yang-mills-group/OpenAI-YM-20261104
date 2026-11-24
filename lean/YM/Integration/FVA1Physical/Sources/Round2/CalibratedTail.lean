import YM.Integration.FVA1Physical.Sources.Round2.UniformWindows
import YM.Integration.FVA1Physical.Sources.Round2.CrossingTail

/-! Tail prices for the actual single and mixed forced rows in the same
calibrated blocking window as the physical estimates. -/

namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics

open Lattice RG Wilson RG.Supply Input Org Source Extra.Histories LocalLTE LocalLTE.Sail
open ConnectedActivityE6 MergeProof MergeProof.Accent Push.AbsoluteSums
open scoped BigOperators Classical

variable {G : Gauge} {X : Metals G} {R : Rolls X.p} {A : Alloy X R} {P : Bolt A}
variable {N n i : ℕ} {I : Type} [DecidableEq I] [Fintype I]

def crossingTailStage (B : Marker.Census I) (Y : Batch (Issue.trail P) N n I)
    (π : ∀ j : ℕ, j ≤ N → Y.steering j) (hi : i < N)
    (O : Appendix B ((Issue.trail P).rep N n i))
    (V : ∀ d, Music ((Labels.frames G).level d) (Issue.trail P) N n) (p₀ : ℕ) : Prop :=
  let H := Issue.trail P
  let Q := H.rep N n i
  let E := Coat.gStep (H.rep N n (i+1)).beta ^ ((p₀ : ℝ) + 1)
  let κ := Real.sqrt (A.B.a.clock.forcedAllowance i)
  ∀ (S : Support (H.S.side i n)) (j : I), Y.origin i j ∈ S →
    ∀ (v : Config G (H.S.side i n)) (r : ℕ),
    Healthy Q.p.threshold (halo (r * Push.GridApprox.Attach.leg Q.p.B) S) v →
    ∀ σ : ℝ, 0 ≤ σ →
      SumBudget (fun k : ℕ × ℕ => if j ∈ (O.truth.marks k.1 k.2).val then
        Marker.Poly.toll (fun _ => 1) (O.truth.marks k.1 k.2) *
          (Real.exp ((Q.p.supportExponent - σ) * coverNumber Q.p.B (Q.activities.forced k.1).support) *
            ‖O.truth.entries k.1 k.2 v‖) else 0) (Real.exp (-σ * r) * (E * κ)) ∧
      SumBudget (fun k : ℕ =>
        Real.exp ((Q.p.supportExponent - σ) * coverNumber Q.p.B (Q.activities.forced k).support) *
          ‖(Y.named V (π i hi.le) j).forced k v‖) (Real.exp (-σ * r) * (κ * (E + E)))

end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics

namespace YM.PhysicalNext.Repeat.Legato.Round2

open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Bandage LocalLTE LocalLTE.Sail MergeProof MergeProof.Accent

/-- One calibrated construction for the prescribed order, field horizon,
marker load and window width. The constant in the physical error is independent of volume,
initial cutoff, marks and field coefficients within those budgets. At a healthy anchor
only forced boxes crossing from marks to the exterior can change the gas. -/
theorem calibratedCrossingWindows {G : Gauge} (hG : G.Simple) (p K TT D₀ : ℕ) :
    ∃ (X : Metals G) (D : Rolls X.p) (A : Alloy X D) (P : Bolt A)
      (r₀ : ℕ → ℕ)
      (T : ∀ d N n, TransferData ((Labels.frames G).level d) (Issue.trail P) N n)
      (V : ∀ N n d, Music ((Labels.frames G).level d) (Issue.trail P) N n),
      let H := Issue.trail P
      let C := Family.mk H (hol G) (Labels.frames G) (localSection G) r₀ T
      OPE.Therm.Poetry H.levels ∧ Spec.Calibrated C ∧ C.Makes ∧
        (∀ᶠ i : ℕ in atTop, ∀ (N n : ℕ) (_ : i ≤ N) (S : Support (H.S.side i n)),
          (OPE.Therm.scene H N n i).real {v | ¬ Healthy (H.rep N n i).p.threshold S v} ≤
            ((S.card * 5 ^ 4 * Fintype.card PlaqAxes : ℕ) : ℝ) * OPE.Therm.vanishP H.levels i) ∧
        ∀ (I : Type) [DecidableEq I] [Fintype I] (B : Marker.Census I) (N n m : ℕ),
          m < N → N - m ≤ TT + 1 → ∀ (Y : Batch H N n I), Nonempty I →
          Y.Wants m r₀ K → (∀ j, Y.demand j ≤ D₀) →
          (∀ j, Y.wavelengths j = ((A.B.a.S.a N : ℂ) ^ Y.demand j) •
            stepUp (Y.motion j) (Y.origin N j)
              (C.O N n ((T (Y.demand j) N n).terminal (Y.voice j)) 0)) ∧
          Nonempty (∀ j : ℕ, j ≤ N → Y.steering j) ∧
          ∀ π : ∀ j : ℕ, j ≤ N → Y.steering j,
            ∃ (fields : ∀ (j : I) (s : ℕ), ((Labels.frames G).level (Y.demand j)).Coeff →
                Coefficient ((Labels.frames G).level (Y.demand j)) (H.S.side s n))
              (O : ∀ s : ℕ, Appendix B (H.rep N n s)),
              ∀ (i : ℕ), m ≤ i → ∀ hi : i < N,
                Harmonics.uniformStage B Y π fields hi (O i) (V N n) D₀ K TT p ∧
                Harmonics.crossingStage B Y π fields hi (O i) (V N n) ∧
                Harmonics.crossingTailStage B Y π hi (O i) (V N n)
                  (look K (Harmonics.upgradedOrder G D₀ K p) TT) := by
  obtain ⟨X, D, A, _, _, _, _, _, _, _, _, _, _, P, _, hPoetry, _, _, _, _, _, _, _,
      r₀, T, hcal, hmakes, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, hs⟩ :=
    engineWithPoetry (hG := hG) (p := Harmonics.upgradedOrder G D₀ K p) (n := 0) (d := 0) (Mζ := 0) (b := 0)
      (CB := K) (MB := 0) (J' := 0) (μ := 0) (B' := 0) (η := 1) (κ := 1)
      (hκ := zero_lt_one) (hJ := le_rfl) (hx := le_rfl) (hz := zero_lt_one) (TT := TT)
  obtain ⟨V, hreg, controls⟩ := hs.controls
  refine ⟨X, D, A, P, r₀, T, V, hPoetry, hcal, hmakes,
    YM.Integration.FVA1Physical.anchoredFlag_probability P.choice hPoetry hG, ?_⟩
  intro I _ _ B N n m hm hwindow Y hI hy hd
  obtain ⟨v₀⟩ := hI
  obtain ⟨hbirth, hsteer, outputs⟩ := controls I B N n m hm hwindow Y v₀ hy
  refine ⟨hbirth, hsteer, ?_⟩
  intro π
  obtain ⟨F, O, hO⟩ := outputs π (fun j => FrameBox.cane (0 : Site (A.B.a.S.side j n)))
  refine ⟨F, O, ?_⟩
  intro i hmi hi
  obtain ⟨frame, fine⟩ := hO.chisels i hmi hi
  obtain ⟨_, panel⟩ := hO.chain.2 i hmi hi
  obtain ⟨_, _, _, _, _, _, _, _, printer, hout⟩ := panel.permits
  have hprep := printer.exactQ
  rw [← hout] at hprep
  have hroles : Y.Roles (V N n) m _ r₀ K :=
    ⟨hy, fun j => (hreg (Y.demand j) N n ((hy.registered j).trans hm.le)).2.contract⟩
  have hnamed j := (Y.financed (V N n) (π i hi.le) hroles hmi hi.le j).1
  have hstage := Harmonics.allFlagStage_of_finePrint B Y π F hi (O i) (V N n) fine hprep
    hnamed (fun j => (frame j).receipt)
  refine ⟨Harmonics.uniformStage_of_allFlags B Y π F hi (O i) (V N n) hG hPoetry
    (by omega) hd hy.lines hy.marks hstage, ?_⟩
  constructor
  · intro S v hv
    exact LocalLTE.Sail.Round2.retainedForecast_crossing B _ (O i) (Y.origin i) _ hnamed
      hprep.plate S v hv (Harmonics.spectralValue Y π F hi)
  have hrad := printer.auditX
  rw [← hout] at hrad
  intro S j hj v r hv σ hσ
  constructor
  · apply LocalLTE.Sail.Round2.mixedCrossingTail _ _ hprep.entire _ hrad.trueB S j _ v r hv σ hσ
    simpa only [hprep.pins] using hj
  let Rj := LocalLTE.Vinca.decrement (Y.named (V N n) (π i hi.le) j) (Harmonics.pointF Y π F hi j)
  have hz : Rj.forced = (Y.named (V N n) (π i hi.le) j).forced := by
    change (Y.named (V N n) (π i hi.le) j).forced - (Harmonics.pointF Y π F hi j).forced = _
    rw [(frame j).stocks, sub_zero]
  simpa only [hz] using LocalLTE.Sail.Round2.singleCrossingTail _ Rj (frame j).trade
    ((frame j).earns.bound le_rfl) S hj v r hv σ hσ

end YM.PhysicalNext.Repeat.Legato.Round2
