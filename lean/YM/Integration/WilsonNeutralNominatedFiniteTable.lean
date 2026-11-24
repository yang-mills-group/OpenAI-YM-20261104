import YM.Integration.WilsonNeutralCopiedProgram
import YM.Integration.WilsonMarkedIndependentConnectedHistory

/-! The independently computed finite and covered contractions of all the
actual thermometer fields use one common fitted top and measured coupling. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonNeutralNominatedFiniteTable
open Function Filter Lattice Laurent Exterior Wilson RG Precision Tree Matrix Bloch
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Mesa Next.Free Stationary Work.F08
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Soil WilsonCoeffUV.Shard WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider PhysicalNext.Repeat.Legato Labels Source Next.Foundations
open WilsonNeutralCopiedProgram WilsonNeutralOffsetCutoff
open WilsonConditionalTaylorWheelConnectedReadout
open scoped Classical Matrix BigOperators Topology
variable {G : Gauge} (R : Run G)
local notation "V" => R.family.path.levels
local notation "d" => WilsonOriginalThermometerPalette.levels

def top (A : WilsonPositionThermometerCapStation.Group R.family 6) (N per : ℕ) (caps : Fin 3 → ℕ)
    (w : ∀ i, d i < caps i) (phase : Fin 3 → ℂ →ₗ[ℝ] ℝ) : Outerm G caps :=
  let g := ConnectedActivityE6.Coat.gStep (R.family.beta N per)
  coatA V R.metals.O N N (deck (G:=G) d caps w)
    (fun i => submitted R N per (named R A N per i) (phase i) g)

theorem healthy (A : WilsonPositionThermometerCapStation.Group R.family 6) (N per : ℕ) (caps : Fin 3 → ℕ)
    (w : ∀ i, d i < caps i) (phase : Fin 3 → ℂ →ₗ[ℝ] ℝ) :
    Wellness d (top R A N per caps w phase) := by
  let g := ConnectedActivityE6.Coat.gStep (R.family.beta N per)
  let Q := deck (G:=G) d caps w
  let v := fun i => submitted R N per (named R A N per i) (phase i) g
  have init (z : Fin 3 → Cover) := birth R d caps w N per (named R A N per) phase g z
  refine ⟨fun z => (init z).2 ∅ (by simp), fun z S => ?_, fun z z' S eq => ?_⟩
  · by_cases h : S.card = 1
    · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp h
      rw [show top R A N per caps w phase z {i} = _ from (init z).1 i, mass, Finset.sum_singleton, ← filed]
      have fresh : Shimmer (Peaks V R.metals.O (R.family.localSection (d i)) (w i) N N) := by
        rw [Peak_initial]
        exact freshly _ R.family.params (w i) (R.makes.sections _) (Next.Foundations.valuation G _)
      exact ((On_auth (Shrine_on _ fresh _ le_rfl)).tuft (petal caps i)).shifted _
    · rw [show top R A N per caps w phase z S = 0 from (init z).2 S h]
      exact unstamped
  · by_cases h : S.card = 1
    · obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp h
      change coatA V R.metals.O N N Q v z {i} = coatA V R.metals.O N N Q v z' {i}
      rw [coatLeaf,coatLeaf,eq _ (by simp)]
    · exact ((init z).2 S h).trans ((init z').2 S h).symm

private theorem cap (S : Finset (Fin 3)) : mass d S ≤ 14 := by
  calc mass d S ≤ mass d Finset.univ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 14 := by decide

/-- All masks and all sites, including the mixed deposits at every later
filing, use the same independently submitted original cutoff columns. -/
theorem original (simple : G.Simple) (menu : ℕ → Gear G → ℝ)
    (funded : FundedMarkedCoverRows.prices menu R.kit) (color : G.ColorIndex)
    (tags : ∀ i n, (FormalBulk08.Flat.primary ((V).clock.op i 0).patch (V).clock.kernel n).Choices)
    (A : WilsonPositionThermometerCapStation.Group R.family 6) (N per : ℕ) (caps : Fin 3 → ℕ)
    (w : ∀ i, d i < caps i) (phase : Fin 3 → ℂ →ₗ[ℝ] ℝ) (a : Loc G 1)
    (z : Fin 3 → Cover) :
    let seed := top R A N per caps w phase
    (∀ i U, WilsonNeutralCopiedField.copied R N per (named R A N per i) (wrap (R.family.side N per) (z i)) U =
      R.family.O N per (named R A N per i) (wrap (R.family.side N per) (z i)) U) ∧
      ∀ j ≤ N, ∀ (test : Case caps) (S : Finset (Fin 3)) (n : Side),
        let T := Gears V R.metals.O d d N N j seed z
        finiteRead test S n (T S) =
          WilsonMarkedIndependentConnectedHistory.finite R color tags N N j d seed z test S n ∧
        read test S (T S) =
          WilsonMarkedIndependentConnectedHistory.cover R color N N j 14 d seed z test S := by
  intro seed
  refine ⟨fun i U => congrFun (WilsonNeutralCopiedField.elected R N per _ _) U,?_⟩
  intro j hj test S n
  exact WilsonMarkedIndependentConnectedHistory.original R color tags simple menu funded hj le_rfl d d
    seed (healthy R A N per caps w phase) a z test S n 14 (cap S)

end YM.Integration.WilsonNeutralNominatedFiniteTable

