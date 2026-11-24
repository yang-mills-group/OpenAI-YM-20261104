import YM.Integration.WilsonIndependentCapturedContrastAppointment
import YM.Integration.WilsonIndependentCapturedScale
import YM.Integration.WilsonIndependentCapturedDates
import YM.Integration.WilsonPositionProgramInfraredAtlas

/-! A signed change of the captured word, tested against the later
prescribed multi-field Rocket on its original reporting band. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 550000
namespace YM.Integration.WilsonIndependentCapturedRocketPrice
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Budget RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform
open RegulatorIR.Oracle RegulatorIR.Epoch RegulatorIR.Atlas RegulatorIR.Calibration RegulatorIR.Profiles
open RegulatorIR.Taping RegulatorIR.Halo RegulatorIR.FVAAlt2 RegulatorIR.Spatial
open WilsonPositionProgramReporterBand WilsonIndependentCapturedCalendar Pert.Asymptotics
open Labels Source YM.FVAAlt2
open scoped ENNReal Classical
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type}
local notation "program" => Oracle.books C.family.path.levels.clock.kernel

theorem original {simple : G.Simple} {axis : Axis} {ε : ℝ}
    (elected : WilsonPositionProgramNestedElection.course simple axis ε C.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested C.kit)
    (slow : WilsonWindowReportingPace.Slow C.kit)
    (branch : ∀ patch : Patch, patch.Branches C.family.path.levels.clock.kernel G) (order P : ℕ) :
    ∃ first : ℕ, ∀ stage ≥ first, ∀ B : Band C D stage, ∀ report : X → ℕ,
      let m := B.lower ∘ report
      let j := B.span ∘ report
      let w := B.powers ∘ report
      let S := WilsonPositionProgramInfraredCircuit.circuit C D m j w (fun x => B.blocks (report x))
      ∀ (color : G.ColorIndex) (F : Tent j), Notebook S (program) G branch color (Rocket.native j) F order →
      ∃ seed : (S.dialect (program) G branch (sheet F)).Primitive (meter C D m j w) order (quantum 1 0),
      ∀ (capture stop : Choice j), capture.age ≤ stop.age →
      let T := capture.after.part (S.dialect (program) G branch (sheet F))
        (S.payroll (program) G branch (sheet F)) seed
      ∀ {frames : Frames G} {charts : Hol G} (basis : Lobby.Registry frames charts)
        {I : Type} [LinearOrder I] (roster : Finset I) (d : I → ℕ)
        (axis : (i : I) → (frames.level (d i)).Index) (z : X → I → Cover),
      let H := Rocket.Ignite S (program) branch F basis roster d axis z
      ∀ (h a off : ℕ) (issued : T.Report h) (residual : T.Report a) (film : X → Portrait G),
        (∀ x, BasisT a off (film x) (residual.main (Page.opening capture.after.spans x))) →
        (∀ x i, i ≤ order → H.main (capture.choose x) i - issued.main (Page.opening capture.after.spans x) i =
          residual.main (Page.opening capture.after.spans x) i) →
        ∀ (root : X → Room) (fee : X → ℝ), (∀ x, 0 ≤ fee x) →
        (∀ i, i ≤ order → ∀ r, Claim (meter C D m j w)
          (fun x => (S.dialect (program) G branch (sheet F)).coverQ root 2 (capture.choose x))
          (fun x => ENNReal.ofReal (fee x)) (fun x => residual.main (Page.opening capture.after.spans x) i r)) →
        ∀ e, e ≤ order → ∀ᶠ t : ℕ in atTop, ∀ x, report x=t →
          ∀ N per : ℕ, B.reporter+t ≤ N →
          let g := regulatorRun C.family N per (B.reporter+t)
          fee x ≤ g^(P+1) →
          ‖Rocket.stopped S (program) branch F basis roster d axis stop z x e -
            note (issued.main ((WilsonIndependentFreshScalar.remaining capture stop).choose x) e 0)‖ ≤ g^P := by
  obtain ⟨start,enroll⟩ := WilsonPositionProgramInfraredAtlas.purchased (X:=X) C D elected paid slow branch order
  obtain ⟨price,cover⟩ := WilsonIndependentCapturedScale.uniform C D simple
  refine ⟨max start price,?_⟩
  intro stage hs B report m j w S color F notebook
  have late (x : X) : start ≤ m x := ((le_max_left _ _).trans hs).trans (B.ready _)
  have basisMesh (x : X) : S.l ((Rocket.native j).choose x) = 1 :=
    div_self (by exact_mod_cast (WilsonPositionProgramInfraredCircuit.count D j w (Page.opening j x)).property.ne')
  have peak (x : X) : (WilsonPositionProgramInfraredAtlas.budget C D m j w (fun x => B.blocks (report x))).peak
      ((Rocket.native j).choose x) = 0 := by
    change Real.log (S.l ((Rocket.native j).choose x)) = 0
    rw [basisMesh,Real.log_one]
  obtain ⟨seed,programmed⟩ := WilsonIndependentCapturedContrastAppointment.original S (program) branch simple
    (show quantum 1 0 ≤ Lodge.through order by simp [quantum,Lodge.through])
    (enroll m j w (fun x => B.blocks (report x)) late) notebook peak basisMesh
    (age C D m j w (fun x => B.blocks (report x)))
  refine ⟨seed,?_⟩
  intro capture stop older T frames charts basis I ord roster d axis z H h a off issued residual film realWord enrolled root fee nonneg wages e he
  have stock (x : X) (i r : ℕ) : Prim.Bounded (H.main (Page.opening j x) i r) :=
    (Rocket.kickLaw basis roster d axis (z x)).1.canopy i r
  obtain ⟨A,l,ap,hear⟩ := programmed _ h a off capture stop older H issued residual film stock realWord
    enrolled root fee nonneg wages e he
  have refund := cover stage ((le_max_right _ _).trans hs) B ap l P 0
  filter_upwards [refund] with t cash x ht N per cut g bound
  have grow : 0 ≤ g := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have row := hear x
  have one : 1 ≤ fare C D m j w x := fare_one C D m j w x
  change ‖Rocket.stopped S (program) branch F basis roster d axis stop z x e - _‖ ≤
    A*(ENNReal.ofReal (fare C D m j w x)).toReal^l*fee x at row
  rw [ENNReal.toReal_ofReal (zero_le_one.trans one)] at row
  have raw : 0 ≤ A*(fare C D m j w x)^l := mul_nonneg ap (pow_nonneg (zero_le_one.trans one) l)
  have wallet := cash N per cut 1 ((g^(P+1))^2) (by simp) (sq_nonneg _) (by simp [g])
  rw [show (((g^(P+1))^2)^((1:ℝ)/2))=g^(P+1) by
    rw [←Real.sqrt_eq_rpow,Real.sqrt_sq (pow_nonneg grow _)], one_mul] at wallet
  apply row.trans ((mul_le_mul_of_nonneg_left bound raw).trans ?_)
  change A*(fare C D B.lower B.span B.powers (report x))^l*g^(P+1) ≤ _
  rw [ht]
  exact wallet

end YM.Integration.WilsonIndependentCapturedRocketPrice
