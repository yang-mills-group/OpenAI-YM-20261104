import YM.Integration.NativeFormalFieldTransition

/-! A funded cutoff schedule converges coefficientwise to the actual
independently calibrated Wilson panel after the finite field and coupling
change. The same moving regulator pays its calibration, positions and stops. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFormalRegulatorCollector

open Function Filter Lattice Labels Precision RG PhysicalNext.Repeat.Legato
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Moving
open MS MS.Local.Physical MS.Menus MS.Land FVA2 FVA2.Verne FVA2.ColorCode FVA2.ArchTurn
open FormalOPE.RG10.Position NativeFormalSharedCoupling NativeFormalPrescriptionAgreement
open WilsonLimitConstruction.FundedFormalEconomy NativePhysicalFieldMatrix
open RG11.Jets
open scoped Classical Topology

variable {G : Gauge} {R : Run G} {hG : G.Simple}

abbrev branches (R : Run G) := ∀ b : Patch, b.Branches R.family.path.levels.clock.kernel G

abbrev program (R : Run G) := Oracle.books R.family.path.levels.clock.kernel

abbrev table (R : Run G) := ∀ d : ℕ, Matrix (FormalOPE.RG10.Position.Deck R.family.labels d)
  (FormalOPE.RG10.Position.Deck R.family.labels d) (PowerSeries ℝ)

def castPrescription {B D : MS.Local.Physical.Deck G} (e : B = D) (P : Prescription D) : Prescription B := e.symm ▸ P

private theorem source {D : MS.Local.Physical.Deck G} (e : nativeDeck R = D) {A : Booked D}
    {M : MS_Data G A} {P : Prescription D} (h : MovingOn R e A M P) :
    ∃ (Z : branches R) (C : Lodge.Contract R (program R) Z),
      Supplier.CorrelationMatch (program R) Z R C
        (e.symm ▸ (⟨A, M⟩ : Data D) : Data (nativeDeck R)).2
        (castPrescription e P) := by
  subst D
  exact h

def schedule (Z : branches R) (C : Lodge.Contract R (program R) Z) (p i : ℕ) :=
  C.floor (program R) Z R + p + i

theorem above (Z : branches R) (C : Lodge.Contract R (program R) Z) (p i : ℕ) :
    C.floor (program R) Z R ≤ schedule Z C p i := by
  unfold schedule
  omega

theorem grows (Z : branches R) (C : Lodge.Contract R (program R) Z) (p : ℕ) :
    Tendsto (schedule Z C p) atTop atTop := by
  apply tendsto_atTop.mpr
  intro m
  filter_upwards [eventually_ge_atTop m] with i hi
  unfold schedule
  omega

def readout (W : Bank R hG) (μ : ℝ) {k : ℝ} (J : PositionX.Bend.Booth k (warehouse R).F)
    (X : Pic.pass (warehouse R) hG W.data J) (d : ℕ) (v : Datum R.family.labels d) :=
  part real ((toComplex (NativeFormalFieldTransition.relative W μ
    (Forge.transfer (warehouse R) W.data J μ X) d)).act
    (series (Forge.Check (warehouse R) W.data J μ X) d) v)

/-- The original finite estimators use an actually funded calibration and
one admissible physical placement and stop sequence. -/
def Converges (W : Bank R hG) (μ : ℝ) {k : ℝ} (J : PositionX.Bend.Booth k (warehouse R).F)
    (X : Pic.pass (warehouse R) hG W.data J) (P : Prescription (nativeDeck R))
    (Z : branches R) (C : Lodge.Contract R (program R) Z) (A : table R) (p : ℕ) (g : G.ColorIndex) : Prop :=
  let t := schedule Z C p
  let ht := above Z C p
  ∃ (F : Calibration.Tent ((C.profile (program R) Z R t ht).entire))
    (x : ℕ → Lattice.Cover) (Λ : ℕ → ℕ),
    Supplier.Funding (program R) Z R C t ht atTop P A p g W.native.2 μ F ∧
    Supplier.Walk (program R) Z R C t ht μ P p atTop x F Λ ∧
    ∀ (I : Type) [Fintype I] [DecidableEq I] (i : I) (S : Marker.Census I),
      Nonempty (ProgramT.Stamp (program R) Z R C t ht F p x S i) ∧
      ∀ (B : ProgramT.Stamp (program R) Z R C t ht F p x S i) (d : ℕ) (v : Datum R.family.labels d),
        YM.FVAAlt2.Moving.Budget.Nice p atTop
          (fun j => ProgramT.Matter (program R) Z R C t ht F p Λ x S i B A j d v)
          (readout W μ J X d v)

def Supported (W : Bank R hG) (μ : ℝ) : Prop :=
  let V := warehouse R
  ∃ (P : Prescription (wings G)) (S : Blaze.ExactSpin V P) (U : Frost.Trusted P)
    (k : ℝ) (J : PositionX.Bend.Booth k V.F) (X : Pic.pass V hG W.data J)
    (Z : branches R) (C : Lodge.Contract R (program R) Z) (D : Drivers)
    (L : Patience (Study.Plan R) D) (A : table R),
    Atoll.Main.Economy hG V W.book W.data P S U J ∧
    MovingOn R (NativeFormalDeckAgreement.moving_deck R) (angular W.book V) W.data P ∧
    YM.FVAAlt2.Mass.Framed (Study.Plan R) L A ∧
    ∀ p : ℕ, 0 < p → ∀ g : G.ColorIndex,
      Converges W μ J X (castPrescription (NativeFormalDeckAgreement.moving_deck R) P) Z C A p g

theorem purchased (W : Bank R hG) (μ : ℝ) : Supported W μ := by
  obtain ⟨P, S, U, k, J, X, E, h, hTarget⟩ := NativeFormalFieldTransition.paid W μ
  obtain ⟨Z, C, receipt⟩ := source (NativeFormalDeckAgreement.moving_deck R) h
  obtain ⟨D, L, A, hA, select⟩ := receipt.tune
  refine ⟨P, S, U, k, J, X, Z, C, D, L, A, E, h, hA, ?_⟩
  intro p hp g
  have hOrder (i : ℕ) : p ≤ schedule Z C p i := by unfold schedule; omega
  obtain ⟨F, hF⟩ := select ℕ g μ atTop inferInstance inferInstance (schedule Z C p) (above Z C p)
    (grows Z C p) p hp.ne' hOrder
  obtain ⟨x, hx⟩ := hF.bearings
  obtain ⟨Λ, hΛ⟩ := hF.fees
  have hWalk : Supplier.Walk (program R) Z R C (schedule Z C p) (above Z C p) μ
      (castPrescription (NativeFormalDeckAgreement.moving_deck R) P) p atTop x F Λ :=
    ⟨hx, hΛ Λ (Eventually.of_forall fun _ => le_rfl)⟩
  refine ⟨F, x, Λ, hF, hWalk, ?_⟩
  intro I _ _ i census
  obtain ⟨hs, hr⟩ := hF.reach x Λ hWalk I inferInstance inferInstance i census
  refine ⟨hs, ?_⟩
  intro B d v
  rw [readout, hTarget d v]
  exact hr B d v

/-- At every prescribed positive penalty one original Run realizes all
finite estimator orders and the original extraction finals. -/
theorem at_penalty (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Run G) (W : Bank R hG), R.family.path.levels.clock.kernel.penalty = ε ∧ Run.Ties R ∧
      (∀ a : Extraction.Order, ∃ (b : Extraction.Order) (T : Table R.family.book),
        Nonempty (Spec.Final R.family (a.refine b) T)) ∧ ∀ μ : ℝ, Supported W μ := by
  obtain ⟨R, hε', hT, hS, h⟩ := NativeFormalEconomyAgreement.at_penalty hG hε
  obtain ⟨B, M, P, S, U, k, J, hb, E, hm⟩ := NativeFormalEconomyAgreement.common R hG h
  let W : Bank R hG := ⟨B, M, P, S, U, k, J, hb, E, hm⟩
  exact ⟨R, W, hε', hT, hS, purchased W⟩

end YM.Integration.NativeFormalRegulatorCollector
end
