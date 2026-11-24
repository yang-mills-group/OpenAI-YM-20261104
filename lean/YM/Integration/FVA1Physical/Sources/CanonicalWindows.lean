import YM.Integration.FVA1Physical.Sources.Correlations

/-! A calibrated physical family admitting the tested finite-window estimates.
The construction can depend on the order, the marker budget and the window
length. Its initial insertions are the terminal fields of this very family. -/

namespace YM.PhysicalNext.Repeat.Legato

open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Bandage LocalLTE LocalLTE.Sail MergeProof MergeProof.Accent

/-- For each prescribed order, finite marker budget and window depth, select
one calibrated, physical family. All admitted finite volumes, cutoffs,
steerings and batches on that family receive the same partition-normalized
error bound at every stage of the window. The coefficients in the forecast
are those produced by C18. -/
theorem canonicalFieldWindows {G : Gauge} (hG : G.Simple) (p K TT : ℕ) :
    ∃ (X : Metals G) (D : Rolls X.p) (A : Alloy X D) (P : Bolt A)
      (r₀ : ℕ → ℕ)
      (T : ∀ d N n, TransferData ((Labels.frames G).level d) (Issue.trail P) N n),
      let H := Issue.trail P
      let C := Family.mk H (hol G) (Labels.frames G) (localSection G) r₀ T
      Spec.Calibrated C ∧ C.Makes ∧
        ∀ (I : Type) [DecidableEq I] [Fintype I] (B : Marker.Census I) (N n m : ℕ),
          m < N → N - m ≤ TT + 1 → ∀ (Y : Batch H N n I), Nonempty I →
          Y.Wants m r₀ K →
          (∀ j, Y.wavelengths j = ((A.B.a.S.a N : ℂ) ^ Y.demand j) •
            stepUp (Y.motion j) (Y.origin N j)
              (C.O N n ((T (Y.demand j) N n).terminal (Y.voice j)) 0)) ∧
          Nonempty (∀ j : ℕ, j ≤ N → Y.steering j) ∧
          ∀ π : ∀ j : ℕ, j ≤ N → Y.steering j,
            ∃ (fields : ∀ (j : I) (s : ℕ), ((Labels.frames G).level (Y.demand j)).Coeff →
                Coefficient ((Labels.frames G).level (Y.demand j)) (H.S.side s n))
              (O : ∀ s : ℕ, Appendix B (H.rep N n s)),
              ∀ (i : ℕ), m ≤ i → ∀ hi : i < N,
                Harmonics.physicalTestedStage B Y π fields hi (O i) p K ∧
                Harmonics.physicalTerminalStage B Y π fields hi (O i) p K := by
  obtain ⟨X, D, A, _, _, _, _, _, _, _, _, _, _, P, _, _, _, _, _, _, _, _,
      r₀, T, hcal, hmakes, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, hs⟩ :=
    engineCanonical (hG := hG) (p := p) (n := 0) (d := 0) (Mζ := 0) (b := 0)
      (CB := K) (MB := 0) (J' := 0) (μ := 0) (B' := 0) (η := 1) (κ := 1)
      (hκ := zero_lt_one) (hJ := le_rfl) (hx := le_rfl) (hz := zero_lt_one) (TT := TT)
  obtain ⟨V, _, controls⟩ := hs.controls
  refine ⟨X, D, A, P, r₀, T, hcal, hmakes, ?_⟩
  intro I _ _ B N n m hm hwindow Y hI hy
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
  have hstage := Harmonics.physicalTestedStage_of_finePrint B Y π F hi (O i)
    (V N n) fine (fun j => (frame j).receipt) hprep.shelf printer.measurableX
  exact ⟨hstage, Harmonics.physicalTerminalStage_of_readout B Y π F hi (O i) hstage⟩

end YM.PhysicalNext.Repeat.Legato
