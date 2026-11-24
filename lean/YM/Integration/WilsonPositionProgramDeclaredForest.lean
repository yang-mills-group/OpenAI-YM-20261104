import YM.Integration.WilsonPositionProgramSubmittedSpoken

/-! The finite original block compiler identifies both occupied and unmarked
coefficients at every held coarse direction of the submitted program. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramDeclaredForest
open Exterior Wilson Precision Filter Set Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.FVAAlt2
open RegulatorIR.FVAAlt2.Period.Field RegulatorIR.FVAAlt2.Pipeline RegulatorIR.Calibration
open WilsonPositionProgramVariableCircuit
open scoped Classical Topology PowerSeries
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type} (m j : X→ℕ) (w : X→ℕ→ℕ)
    (blocks : ∀ x k, (C.family.S.block (m x+k)).val=D.ratio^(w x k))
    (branch : ∀ P : RG.Patch, P.Branches C.family.path.levels.clock.kernel G)
local notation "H" => WilsonPositionProgramInfraredCircuit.history C D m j w blocks
local notation "E" => WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
local notation "K" => RunFormalChain.fromRun C
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel

theorem original (color : G.ColorIndex) (r : ℕ) (F : Tent j)
    (hF : Notebook E Y G branch color (Rocket.native j) F r) :
    ∃ T : See.Times (sheet F) r, ∀ (I : Type) [LinearOrder I] [Fintype I] (z : X→I→ Cover)
      (A : Type) [DecidableEq A] [Fintype A] (mask : Marker.Census A) (u : A),
      ∃ V : (per : ℕ) → Sound.Figure.Activation (I:=I) C H per mask,
      (∀ per, Sound.Figure.Course C H z (sheet F) per u mask r T (V per)) ∧
      (∀ per (d : I→ℕ) (a : (a:I)→(C.family.labels.level (d a)).Index) (page : Page j)
        (U : fieldDir G (C.family.side ((H).vol page) per) 1) (e : ℕ), e≤r →
        let src := Sound.Figure.prop C z d a
        let actual := (V per d a) page
        let records := (H).records (E) C.family.path per page
        See.prime H mask u (sheet F) per r T (V per d a) (x:=page) U e =
          Booth.Uniforms.cuff (See.observe branch K H src (sheet F) per page) (Kick.depthF Finset.univ d a) e U ∧
        See.visible mask records.clip records.path (T.cloth page) actual e U =
          Booth.Uniforms.cloth records.clip records.path (See.work branch K H (sheet F) per page) e U) ∧
          ∀ {deck : MS.Local.Physical.Deck G} (labels : I → MS.Rake.Label deck) (Q : MS.Land.Prescription deck)
            (station : Ledger.Choice j) (y fee : X → ℝ) (x : X) (e : ℕ), e ≤ r →
            Tendsto (fun per => PowerSeries.coeff e (Sound.Formal.dated Q (y x) (Lodge.basisR C) labels (fee x)
              (Sound.Figure.spoken C H (sheet F) per u mask r T (V per) (station.choose x)))) atTop
              (𝓝 (PowerSeries.coeff e (Rocket.adjust E Y branch F (Lodge.basisR C) station labels z Q y fee x))) := by
  have start := Sound.flatTop Y branch hF
  obtain ⟨T,registered⟩ := WilsonPositionProgramSubmittedSpoken.spoken C D m j w blocks branch color r F hF
  refine ⟨T,?_⟩
  intro I _ _ z A _ _ mask u
  obtain ⟨V,course,bank⟩ := registered I z A mask u
  refine ⟨V,course,?_,bank⟩
  intro per d a page U e he
  exact See.observes Y branch K H mask u (Sound.Figure.prop C z d a) (sheet F) per r T start
    (course per d a) page U he

end YM.Integration.WilsonPositionProgramDeclaredForest
