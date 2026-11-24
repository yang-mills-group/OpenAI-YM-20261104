import YM.Integration.WilsonPositionProgramInfraredCircuit
import YM.Integration.WilsonPositionProgramVariableHistory

/-! The original signed block-program reading at any filed age of a common variable circuit. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramSubmittedSpoken
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.FVAAlt2
open RegulatorIR.FVAAlt2.Period.Field RegulatorIR.FVAAlt2.Pipeline RegulatorIR.Calibration
open WilsonPositionProgramVariableCircuit
open scoped Classical Topology PowerSeries
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type} (m j : X → ℕ) (w : X → ℕ → ℕ)
    (blocks : ∀ x k, (C.family.S.block (m x+k)).val=D.ratio^(w x k))
    (branch : ∀ P : RG.Patch, P.Branches C.family.path.levels.clock.kernel G)
local notation "H" => WilsonPositionProgramInfraredCircuit.history C D m j w blocks
local notation "E" => WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
local notation "K" => RunFormalChain.fromRun C
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel

/-- The same original kinetic/scalar bank serves all tags, placements, rosters and proper faces.
The written limit runs over auxiliary copies at fixed experiment and is independent of the physical cutoffs. -/
theorem spoken (color : G.ColorIndex) (r : ℕ) (F : Tent j)
    (hF : Notebook E Y G branch color (Rocket.native j) F r) :
      ∃ T : See.Times (sheet F) r, ∀ (I : Type) [LinearOrder I] [Fintype I] (z : X → I → Cover)
        (A : Type) [DecidableEq A] [Fintype A] (mask : Marker.Census A) (u : A),
        ∃ V : (per : ℕ) → Sound.Figure.Activation (I:=I) C H per mask,
          (∀ per, Sound.Figure.Course C H z (sheet F) per u mask r T (V per)) ∧
          ∀ {deck : MS.Local.Physical.Deck G} (labels : I → MS.Rake.Label deck) (Q : MS.Land.Prescription deck)
            (station : Ledger.Choice j) (y fee : X → ℝ) (x : X) (e : ℕ), e ≤ r →
            Tendsto (fun per => PowerSeries.coeff e (Sound.Formal.dated Q (y x) (Lodge.basisR C) labels (fee x)
              (Sound.Figure.spoken C H (sheet F) per u mask r T (V per) (station.choose x)))) atTop
              (𝓝 (PowerSeries.coeff e (Rocket.adjust E Y branch F (Lodge.basisR C) station labels z Q y fee x))) := by
  have start := Sound.flatTop Y branch hF
  obtain ⟨T,_⟩ := See.prices (sheet F) r start
  refine ⟨T,?_⟩
  intro I _ _ z A _ _ mask u
  choose V course using fun per => Sound.Figure.universal C branch Y H z (sheet F) per u mask r T start
  refine ⟨V,course,?_⟩
  intro deck labels Q station y fee x e he
  have limit := Sound.Figure.tend C branch Y H z F station labels Q x y fee e
  refine limit.congr' (Filter.Eventually.of_forall fun per => ?_)
  exact (Sound.Figure.credits C branch Y H z (sheet F) per station labels Q (y x) (fee x) x u mask r T
    start (V per) (course per) e he).symm

end YM.Integration.WilsonPositionProgramSubmittedSpoken
end
