import YM.Integration.NativeFormalComplexCollector

/-! For every countable family of smeared physical coefficient tests, one
divergent sequence of actual finite cutoffs on the purchased Run realizes
all their limits. Each station records the original funding, calibration,
marker stamp, placement and stopping time used in its measured coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFormalDiagonalCollector

open Function Filter Lattice Labels Precision RG PhysicalNext.Repeat.Legato
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Moving
open MS MS.Local.Physical MS.Menus MS.Land FVA2 FVA2.Verne FVA2.ColorCode FVA2.ArchTurn
open FormalOPE.RG10.Position NativeFormalSharedCoupling NativeFormalPrescriptionAgreement
open WilsonLimitConstruction.FundedFormalEconomy NativeFormalRegulatorCollector
open scoped Classical Topology BigOperators

variable {G : Gauge} {R : Run G} {hG : G.Simple}

/-- A finite order, separated test and arbitrary independent complex physical inputs. -/
structure Request (F : Frames G) where
  horizon : ℕ
  order : ℕ
  profile : PertExtension.Physical.Profile
  field : Fin profile.n → Pert.Position.E F horizon

def target (W : Bank R hG) (μ : ℝ) {k : ℝ} (J : PositionX.Bend.Booth k (warehouse R).F)
    (X : Pic.pass (warehouse R) hG W.data J) (a : Request R.family.labels) : ℂ :=
  NativeFormalComplexCollector.fields a.field fun z =>
    PowerSeries.coeff a.order (NativeFormalComplexCollector.panel W μ J X a.horizon ⟨a.profile,z⟩)

structure Trial (W : Bank R hG) (μ : ℝ) (P : Prescription (nativeDeck R)) (Z : branches R)
    (C : Lodge.Contract R (program R) Z) (A : table R) (g : G.ColorIndex)
    {I : Type} [Fintype I] [DecidableEq I] (i : I) (S : Marker.Census I) where
  order : ℕ
  station : ℕ
  calibrate : Calibration.Tent ((C.profile (program R) Z R (schedule Z C order) (above Z C order)).entire)
  location : ℕ → Lattice.Cover
  stop : ℕ → ℕ
  stamp : ProgramT.Stamp (program R) Z R C (schedule Z C order) (above Z C order) calibrate order location S i
  paid : Supplier.Funding (program R) Z R C (schedule Z C order) (above Z C order) atTop P A order g W.native.2 μ calibrate
  walked : Supplier.Walk (program R) Z R C (schedule Z C order) (above Z C order) μ P order atTop location calibrate stop

namespace Trial
variable {W : Bank R hG} {μ : ℝ} {P : Prescription (nativeDeck R)} {Z : branches R}
  {C : Lodge.Contract R (program R) Z} {A : table R} {g : G.ColorIndex}
  {I : Type} [Fintype I] [DecidableEq I] {i : I} {S : Marker.Census I}

def cutoff (T : Trial W μ P Z C A g i S) : ℕ := schedule Z C T.order T.station

def measure (T : Trial W μ P Z C A g i S) (a : Request R.family.labels) : ℂ :=
  let E := ProgramT.Matter (program R) Z R C (schedule Z C T.order) (above Z C T.order)
    T.calibrate T.order T.stop T.location S i T.stamp A T.station a.horizon
  NativeFormalComplexCollector.fields a.field fun w =>
    Complex.mk (PowerSeries.coeff a.order (E ⟨a.profile,w⟩))
      (PowerSeries.coeff a.order (E (NativeFormalComplexCollector.rotate ⟨a.profile,w⟩)))

theorem order_le (T : Trial W μ P Z C A g i S) : T.order ≤ T.cutoff := by
  unfold cutoff schedule
  omega

end Trial

variable (W : Bank R hG) (μ : ℝ) {k : ℝ} (J : PositionX.Bend.Booth k (warehouse R).F)
  (X : Pic.pass (warehouse R) hG W.data J) (P : Prescription (nativeDeck R))
  (Z : branches R) (C : Lodge.Contract R (program R) Z) (A : table R)

private theorem finite (g : G.ColorIndex) {I : Type} [Fintype I] [DecidableEq I] (i : I) (S : Marker.Census I)
    (buy : ∀ p : ℕ, 0 < p → NativeFormalComplexCollector.Converges W μ J X P Z C A p g)
    (s : Finset (Request R.family.labels)) (q : ℕ) :
    ∃ T : Trial W μ P Z C A g i S, q + 1 ≤ T.order ∧
      ∀ a ∈ s, dist (T.measure a) (target W μ J X a) < 1 / (q + 1 : ℝ) := by
  let p := q + 1 + ∑ a ∈ s, a.order
  have hq : q + 1 ≤ p := Nat.le_add_right _ _
  have hp : 0 < p := (Nat.zero_lt_succ q).trans_le hq
  obtain ⟨F, x, Λ, funds, walk, terms⟩ := buy p hp
  obtain ⟨⟨B⟩, hB⟩ := terms I i S
  let T (j : ℕ) : Trial W μ P Z C A g i S := ⟨p, j, F, x, Λ, B, funds, walk⟩
  have horder (a : s) : a.val.order ≤ p := by
    have he := Finset.single_le_sum (f := Request.order) (fun b _ => Nat.zero_le b.order) a.property
    dsimp only [p]
    omega
  have hc (a : s) : Tendsto (fun j => (T j).measure a.val) atTop (𝓝 (target W μ J X a.val)) :=
    (hB B a.val.horizon a.val.order (horder a)).2 a.val.profile a.val.field
  have hnear (a : s) : ∀ᶠ j in atTop,
      dist ((T j).measure a.val) (target W μ J X a.val) < 1 / (q + 1 : ℝ) :=
    Metric.tendsto_nhds.mp (hc a) _ (by positivity)
  obtain ⟨j, hj⟩ := (Filter.eventually_all.2 hnear).exists
  exact ⟨T j, hq, fun a ha => hj ⟨a,ha⟩⟩

def Diagonal : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (i : I) (S : Marker.Census I)
    (g : G.ColorIndex) (u : ℕ → Request R.family.labels),
    ∃ T : ℕ → Trial W μ P Z C A g i S,
      (∀ q, q + 1 ≤ (T q).order) ∧ Tendsto (fun q => (T q).cutoff) atTop atTop ∧
      ∀ m, Tendsto (fun q => (T q).measure (u m)) atTop (𝓝 (target W μ J X (u m)))

theorem realize (buy : ∀ p : ℕ, 0 < p → ∀ g : G.ColorIndex,
    NativeFormalComplexCollector.Converges W μ J X P Z C A p g) : Diagonal W μ J X P Z C A := by
  intro I _ _ i S g u
  let s (q : ℕ) := (Finset.range (q + 1)).image u
  choose T hT near using fun q => finite W μ J X P Z C A g i S (fun p hp => buy p hp g) (s q) q
  refine ⟨T, hT, ?_, ?_⟩
  · apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with q hq
    exact hq.trans ((Nat.le_succ q).trans ((hT q).trans (T q).order_le))
  · intro m
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hsmall : ∀ᶠ q : ℕ in atTop, 1 / (q + 1 : ℝ) < ε :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (eventually_lt_nhds hε)
    filter_upwards [hsmall, eventually_ge_atTop m] with q hεq hmq
    have hm : u m ∈ s q := Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (by omega), rfl⟩
    exact (near q (u m) hm).trans hεq

/-- One directed family handles every finite collection of field and profile
tests, with arbitrary real accuracy and every perturbative order. -/
abbrev Demand (F : Frames G) := Finset (Request F) × ℕ

def AllTests : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (i : I) (S : Marker.Census I) (g : G.ColorIndex),
    ∃ T : Demand R.family.labels → Trial W μ P Z C A g i S,
      (∀ z, z.2 + 1 ≤ (T z).order) ∧ Tendsto (fun z => (T z).cutoff) atTop atTop ∧
      ∀ a : Request R.family.labels, Tendsto (fun z => (T z).measure a) atTop (𝓝 (target W μ J X a))

theorem universal (buy : ∀ p : ℕ, 0 < p → ∀ g : G.ColorIndex,
    NativeFormalComplexCollector.Converges W μ J X P Z C A p g) : AllTests W μ J X P Z C A := by
  intro I _ _ i S g
  choose T hT near using fun z : Demand R.family.labels => finite W μ J X P Z C A g i S
    (fun p hp => buy p hp g) z.1 z.2
  refine ⟨T, hT, ?_, ?_⟩
  · apply tendsto_atTop.mpr
    intro b
    apply (eventually_ge_atTop ((∅, b) : Demand R.family.labels)).mono
    intro z hz
    exact hz.2.trans ((Nat.le_succ z.2).trans ((hT z).trans (T z).order_le))
  · intro a
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hsmall : ∀ᶠ q : ℕ in atTop, 1 / (q + 1 : ℝ) < ε :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (eventually_lt_nhds hε)
    obtain ⟨b,hb⟩ := eventually_atTop.1 hsmall
    apply (eventually_ge_atTop (({a}, b) : Demand R.family.labels)).mono
    intro z hz
    exact (near z a (hz.1 (Finset.mem_singleton_self a))).trans (hb z.2 hz.2)

def Supported (W : Bank R hG) (μ : ℝ) : Prop :=
  let V := warehouse R
  ∃ (P : Prescription (wings G)) (S : Blaze.ExactSpin V P) (U : Frost.Trusted P)
    (k : ℝ) (J : PositionX.Bend.Booth k V.F) (X : Pic.pass V hG W.data J)
    (Z : branches R) (C : Lodge.Contract R (program R) Z) (D : Drivers)
    (L : Patience (Study.Plan R) D) (A : table R),
    Atoll.Main.Economy hG V W.book W.data P S U J ∧
    MovingOn R (NativeFormalDeckAgreement.moving_deck R) (angular W.book V) W.data P ∧
    YM.FVAAlt2.Mass.Framed (Study.Plan R) L A ∧
    Diagonal W μ J X (castPrescription (NativeFormalDeckAgreement.moving_deck R) P) Z C A ∧
    AllTests W μ J X (castPrescription (NativeFormalDeckAgreement.moving_deck R) P) Z C A

theorem purchased (W : Bank R hG) (μ : ℝ) : Supported W μ := by
  obtain ⟨P, S, U, k, J, X, Z, C, D, L, A, E, h, hf, pay⟩ := NativeFormalComplexCollector.purchased W μ
  exact ⟨P, S, U, k, J, X, Z, C, D, L, A, E, h, hf, realize W μ J X _ Z C A pay, universal W μ J X _ Z C A pay⟩

theorem at_penalty (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Run G) (W : Bank R hG), R.family.path.levels.clock.kernel.penalty = ε ∧ Run.Ties R ∧
      (∀ a : Extraction.Order, ∃ (b : Extraction.Order) (T : Table R.family.book),
        Nonempty (Spec.Final R.family (a.refine b) T)) ∧ ∀ μ : ℝ, Supported W μ := by
  obtain ⟨R, W, he, ht, hf, _⟩ := NativeFormalComplexCollector.at_penalty hG hε
  exact ⟨R, W, he, ht, hf, purchased W⟩

end YM.Integration.NativeFormalDiagonalCollector
end
