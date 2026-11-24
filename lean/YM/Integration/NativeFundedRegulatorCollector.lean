import YM.Integration.NativeFormalDiagonalCollector
import YM.Integration.NativeFormalHorizonTransport

/-! All finite regulator coefficients belong to the very same specified
position-normalized pass, matched counterterms and original FVA2 packing
selected on the funded Run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFundedRegulatorCollector

open Function Filter Lattice Labels Precision RG RG.Supply PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Moving
open MS MS.Local.Physical MS.Menus MS.Land FVA2 FVA2.Verne FVA2.ColorCode FVA2.ArchTurn
open FormalOPE.RG10.Position NativeFormalSharedCoupling NativeFormalPrescriptionAgreement
open WilsonLimitConstruction WilsonLimitConstruction.FundedFormalEconomy NativeFormalRegulatorCollector
open RG11.Jets RG11.Horizon
open scoped Classical Topology

universe v
variable {G : Gauge} {R : Run G} {hG : G.Simple}

/-- Both the relative change and its action on the specified physical
panel restrict exactly to every smaller physical field window. -/
def Projective (W : Bank R hG) (μ : ℝ) {k : ℝ} (J : PositionX.Bend.Booth k (warehouse R).F)
    (X : Pic.pass (warehouse R) hG W.data J) : Prop :=
  let p := Forge.transfer (warehouse R) W.data J μ X
  ∀ (d H : ℕ) (h : d ≤ H),
    restrict (NativePhysicalFieldHorizon.includeDeck R.family.labels h) (NativeFormalFieldTransition.relative W μ p H) =
      NativeFormalFieldTransition.relative W μ p d ∧
    slice (NativePhysicalFieldHorizon.includeDeck R.family.labels h) (NativeFormalComplexCollector.panel W μ J X H) =
      NativeFormalComplexCollector.panel W μ J X d

def Realizes (W : Bank R hG) (μ : ℝ) (P : Prescription (wings G)) {k : ℝ}
    (J : PositionX.Bend.Booth k (warehouse R).F) (X : Pic.pass (warehouse R) hG W.data J) : Prop :=
  let T := castPrescription (NativeFormalDeckAgreement.moving_deck R) P
  MovingOn R (NativeFormalDeckAgreement.moving_deck R) (angular W.book (warehouse R)) W.data P ∧
  NativeFormalFieldTransition.Reconstructs W μ J X ∧ Projective W μ J X ∧
  ∃ (Z : branches R) (C : Lodge.Contract R (program R) Z) (D : Drivers)
    (L : Patience (Study.Plan R) D) (A : table R),
    YM.FVAAlt2.Mass.Framed (Study.Plan R) L A ∧
    (∀ p : ℕ, 0 < p → ∀ g : G.ColorIndex, NativeFormalComplexCollector.Converges W μ J X T Z C A p g) ∧
    NativeFormalDiagonalCollector.Diagonal W μ J X T Z C A ∧ NativeFormalDiagonalCollector.AllTests W μ J X T Z C A

private theorem native {D : MS.Local.Physical.Deck G} (e : nativeDeck R = D) {A : Booked D}
    {M : MS_Data G A} {P : Prescription D} (h : MovingOn R e A M P) :
    ∃ (Z : branches R) (C : Lodge.Contract R (program R) Z),
      Supplier.CorrelationMatch (program R) Z R C
        (e.symm ▸ (⟨A, M⟩ : Data D) : Data (nativeDeck R)).2 (castPrescription e P) := by
  subst D
  exact h

private theorem collect (W : Bank R hG) (μ : ℝ) {k : ℝ} (J : PositionX.Bend.Booth k (warehouse R).F)
    (X : Pic.pass (warehouse R) hG W.data J) (P : Prescription (nativeDeck R))
    (Z : branches R) (C : Lodge.Contract R (program R) Z) (A : table R) (p : ℕ) (g : G.ColorIndex)
    (F : Calibration.Tent ((C.profile (program R) Z R (schedule Z C p) (above Z C p)).entire))
    (h : Supplier.Funding (program R) Z R C (schedule Z C p) (above Z C p) atTop P A p g W.native.2 μ F) :
    NativeFormalComplexCollector.Converges W μ J X P Z C A p g := by
  apply NativeFormalComplexCollector.of_real
  obtain ⟨x, hx⟩ := h.bearings
  obtain ⟨Λ, hΛ⟩ := h.fees
  have walk : Supplier.Walk (program R) Z R C (schedule Z C p) (above Z C p) μ P p atTop x F Λ :=
    ⟨hx, hΛ Λ (Eventually.of_forall fun _ => le_rfl)⟩
  refine ⟨F, x, Λ, h, walk, ?_⟩
  intro I _ _ i census
  obtain ⟨hs, hr⟩ := h.reach x Λ walk I inferInstance inferInstance i census
  refine ⟨hs, ?_⟩
  intro B d v
  rw [readout, NativeFormalFieldTransition.regulated W μ J X d v]
  exact hr B d v

/-- A specified economy and every one of its supplied passes retain their
actual moving funding, complex coefficient estimator and all-test cutoff net. -/
theorem on_economy (W : Bank R hG) (window : NativeFVAPlateau.Funded R.family.path.levels)
    (P : Prescription (wings G)) (S : Blaze.ExactSpin (warehouse R) P) (U : Frost.Trusted P) {k : ℝ}
    (J : PositionX.Bend.Booth k (warehouse R).F) (E : Atoll.Main.Economy hG (warehouse R) W.book W.data P S U J)
    (μ : ℝ) (X : Pic.pass (warehouse R) hG W.data J) : Realizes W μ P J X := by
  have hm := NativeFormalEconomyAgreement.on_economy R hG window W.book W.data P S U J E
  obtain ⟨Z, C, receipt⟩ := native (NativeFormalDeckAgreement.moving_deck R) hm
  obtain ⟨D, L, A, hA, selection⟩ := receipt.tune
  let T := castPrescription (NativeFormalDeckAgreement.moving_deck R) P
  have paid (p : ℕ) (hp : 0 < p) (g : G.ColorIndex) :
      NativeFormalComplexCollector.Converges W μ J X T Z C A p g := by
    have order (i : ℕ) : p ≤ schedule Z C p i := by unfold schedule; omega
    obtain ⟨F, hF⟩ := selection ℕ g μ atTop inferInstance inferInstance
      (schedule Z C p) (above Z C p) (grows Z C p) p hp.ne' order
    exact collect W μ J X T Z C A p g F hF
  refine ⟨hm, NativeFormalFieldTransition.regulated W μ J X, ?_, Z, C, D, L, A, hA, paid,
    NativeFormalDiagonalCollector.realize W μ J X T Z C A paid,
    NativeFormalDiagonalCollector.universal W μ J X T Z C A paid⟩
  intro d H h
  exact ⟨NativeFormalHorizonTransport.relative W μ _ h, NativeFormalHorizonTransport.selected W μ J X h⟩

theorem selected_pass (W : Bank R hG) (window : NativeFVAPlateau.Funded R.family.path.levels)
    (P : Prescription (wings G)) (S : Blaze.ExactSpin (warehouse R) P) (U : Frost.Trusted P) {k : ℝ}
    (J : PositionX.Bend.Booth k (warehouse R).F) (E : Atoll.Main.Economy hG (warehouse R) W.book W.data P S U J)
    (μ : ℝ) : ∃ X : Pic.pass (warehouse R) hG W.data J, Realizes W μ P J X := by
  obtain ⟨X, _⟩ := E.hymns μ
  exact ⟨X, on_economy W window P S U J E μ X⟩

/-- The complete original packing is retained on this specific MS bank.
Every originally accepted prescription keeps its own full team and passes. -/
def Packing (W : Bank R hG) : Prop :=
  let V := warehouse R
  RadL.Reg W.book ∧ ∃ Q D : Prescription (wings G),
    Matched.AllProfiles W.data (V.diction (wings G)) Q ∧ Matched.AllProfiles W.data (V.diction (wings G)) D ∧
    Clock.rate Q.team = Clock.rate D.team ∧
    ∀ Q' : Prescription (wings G), Matched.AllProfiles W.data (V.diction (wings G)) Q' →
      ∃ (P : Prescription (wings G)) (S : Blaze.ExactSpin V P) (U : Frost.Trusted P)
        (k : ℝ) (J : PositionX.Bend.Booth k V.F),
        Atoll.Main.Economy hG V W.book W.data P S U J ∧ P.team = Q'.team ∧
        ∀ μ : ℝ, ∀ X : Pic.pass V hG W.data J, Realizes W μ P J X

/-- The field data come from the original FVA packing on exactly this Run. -/
theorem of_correlations (R : Run G) (hG : G.Simple) (h : NativeFVAPlateau.Correlations R) :
    ∃ W : Bank R hG, Packing W := by
  let V := warehouse R
  have window := NativeFormalMixedProfiles.windows h
  obtain ⟨B, M, hB, Q, D, hQ, hD, hClock, accounts⟩ := Atoll.Main.joint_M hG V
  obtain ⟨P, S, U, k, J, E, _⟩ := accounts Q hQ
  have hm := NativeFormalEconomyAgreement.on_economy R hG window B M P S U J E
  let W : Bank R hG := ⟨B, M, P, S, U, k, J, hB, E, hm⟩
  refine ⟨W, hB, Q, D, hQ, hD, hClock, ?_⟩
  intro Q' hQ'
  obtain ⟨P', S', U', k', J', E', ht⟩ := accounts Q' hQ'
  exact ⟨P', S', U', k', J', E', ht, on_economy W window P' S' U' J' E'⟩

theorem of_purchase (hG : G.Simple) {Δ : Decal G} {ε : ℝ}
    {Demand : Sheet G → MapPrices → Type v} {extra : ∀ s q, Demand s q → ℕ → ℕ}
    {numeric : ∀ s q, Demand s q → ℕ → ℕ → ℝ}
    {postnumeric : ∀ s q, Demand s q → (ℕ → ℕ) → ℕ → ℕ → ℝ}
    (A : FundedPlateauRun.Purchase Δ ε Demand extra numeric postnumeric) :
    ∃ W : Bank A.run hG, Packing W := of_correlations A.run hG (A.correlations hG)

theorem purchase (hG : G.Simple) (Δ : Decal G) {ε : ℝ} (hε : 0 < ε)
    (Demand : Sheet G → MapPrices → Type v) (available : ∀ s q, Nonempty (Demand s q))
    (extra : ∀ s q, Demand s q → ℕ → ℕ)
    (numeric : ∀ s q, Demand s q → ℕ → ℕ → ℝ)
    (postnumeric : ∀ s q, Demand s q → (ℕ → ℕ) → ℕ → ℕ → ℝ)
    (prediction : FundedCompanySelection.Prediction G) (paid : FundedPredictionSupply.AllPrices (@prediction)) :
    ∃ A : FundedPlateauRun.Purchase Δ ε Demand extra numeric postnumeric,
      prediction A.run.kit ∧ ∃ W : Bank A.run hG, Packing W := by
  obtain ⟨A, h⟩ := FundedPlateauRun.purchase hG Δ hε Demand available extra numeric postnumeric (@prediction) paid
  exact ⟨A, h, of_purchase hG A⟩

end YM.Integration.NativeFundedRegulatorCollector
end
