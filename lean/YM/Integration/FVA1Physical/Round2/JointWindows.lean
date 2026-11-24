import YM.Integration.FVA1Physical.Round2.CircuitDocket
import YM.Integration.FVA1Physical.Sources.Round2.CalibratedTail

/-! Buy the marked C18 windows and the analytic vacuum estimate on a single calibrated family, retaining any additional represented-density program chosen before the family. -/

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
theorem jointPhysicalWindows {G : Gauge} (hG : G.Simple) {goal : YM.Qlocal.Schedule.Goal G}
    (buy : YM.Qlocal.Schedule.Obtainable goal) (p K TT D₀ : ℕ) :
    ∃ (X : Metals G) (D : Rolls X.p) (A : Alloy X D) (F : Factor A) (P : Bolt A) (u : G.ColorIndex)
      (r₀ : ℕ → ℕ)
      (T : ∀ d N n, TransferData ((Labels.frames G).level d) (Issue.trail P) N n)
      (V : ∀ N n d, Music ((Labels.frames G).level d) (Issue.trail P) N n),
      let H := Issue.trail P
      let C := Family.mk H (hol G) (Labels.frames G) (localSection G) r₀ T
      goal X D A F ∧ Docket C u X.O A.B.M A.B.kin ∧ OPE.Therm.Poetry H.levels ∧ Spec.Calibrated C ∧ C.Makes ∧
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
  haveI := hG.nontrivial_color
  have degree : 0 < G.lieDim := by rw [Gauge.lieDim, ← G.colorIso.finrank_eq]; exact Module.finrank_pos
  let u : G.ColorIndex := ⟨0, degree⟩
  obtain ⟨W,clear⟩ := YM.MSbar.Heath.vocals G
  have proposal := (buy.also (coarseRoom_obtainable (G := G))).also
    (YM.Qlocal.Schedule.vacuumInvoice_obtainable hG u W clear)
  obtain ⟨X, D, A, F, _, _, _, _, _, _, _, _, _, P, _, ⟨⟨grant,room⟩,vac⟩, _, hPoetry, _, _, _, _, _, _, _,
      r₀, T, hcal, hmakes, _, _, _, _, _, _, gamma, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, hs⟩ :=
    engineWithProgram (finance := proposal) (hG := hG) (p := Harmonics.upgradedOrder G D₀ K p) (n := 0) (d := 0) (Mζ := 0) (b := 0)
      (CB := K) (MB := 0) (J' := 0) (μ := 0) (B' := 0) (η := 1) (κ := 1)
      (hκ := zero_lt_one) (hJ := le_rfl) (hx := le_rfl) (hz := zero_lt_one) (TT := TT)
  obtain ⟨V, hreg, controls⟩ := hs.controls
  have growth : Tendsto (fun m => (A.B.a.params m).order) atTop atTop := by
    apply tendsto_atTop.2
    intro i
    filter_upwards [eventually_ge_atTop (r₀ i)] with m hm
    exact (Nat.le_succ i).trans (((hmakes.stages i).2 m hm).1)
  have docket := circuit_docket gamma room W hG vac.2.1 u r₀ T (vac.1 growth)
  refine ⟨X, D, A, F, P, u, r₀, T, V, grant, docket, hPoetry, hcal, hmakes,
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
