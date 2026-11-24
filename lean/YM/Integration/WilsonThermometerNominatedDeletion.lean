import YM.Integration.WilsonNeutralNominatedFiniteTable
import YM.Integration.WilsonThermometerFiniteConnectedCells
import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion

/-! Deletion of actual absolute cutoff sites, before alignment of the three-point test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerNominatedDeletion
open Function Set Filter Finset Marker Extra.Trajectories Primitives.GCC.Anchor
open Lattice Laurent Exterior Wilson RG Precision Tree Matrix Bloch FormalBulk08 FormalBulk08.Flat
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonCoeffUV.Soil WilsonCoeffUV.Shard WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider PhysicalNext.Repeat.Legato Labels Source Next.Foundations
open WilsonConditionalTaylorWheelConnectedReadout WilsonThermometerCenteredAlgebra
open Extraction Table Spec Climb Trace.Pilot Next.UVStress Next.Rank RG12 RG17 PhysMS
open XSpace XSpace.Normalize XSpace.Rose WilsonPositionThermometerCapStation
open scoped Classical BigOperators

local notation "J" => Stock.census (Fin 3)
variable {X : Type*}
def Located (P : (Fin 3 → X) → Poly J) : Prop :=
  ∀ x y s, (∀ i ∈ s.val, x i = y i) → (P x).part s = (P y).part s

private def keep (s : (J).Mode) : Names (Stock.census s.val) J where
  e := ⟨Subtype.val,Subtype.val_injective⟩
  visible _ := Finset.mem_univ _

private theorem restricted {P : (Fin 3 → X) → Poly J} (hp : Located P) {s : (J).Mode}
    {x y : Fin 3 → X} (eq : ∀ i ∈ s.val, x i = y i) :
    (keep s).restriction (P x) = (keep s).restriction (P y) := by
  ext t
  apply hp
  intro i hi
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hi
  exact eq _ a.property

private theorem recover {s : (J).Mode} {P Q : Poly J}
    (agree : (keep s).restriction P = (keep s).restriction Q) : P.part s = Q.part s := by
  let allNames : (Stock.census s.val).Mode := ⟨univ,mem_univ _⟩
  have h : (keep s).share allNames = s := by
    apply Subtype.ext
    ext i
    change i ∈ Finset.univ.image (Subtype.val : s.val → Fin 3) ↔ i ∈ s.val
    constructor
    · intro hi; obtain ⟨a,_,rfl⟩ := mem_image.mp hi; exact a.property
    · intro hi; exact mem_image.mpr ⟨⟨i,hi⟩,mem_univ _,rfl⟩
  rw [←h]
  exact congrArg (fun p : Poly (Stock.census s.val) => p.part allNames) agree

theorem exponential {k : (Fin 3 → X) → Poly J} (hk : Located k)
    (quiet : ∀ x, (k x).part (J).quiet = 0) : Located (fun x => Poly.pass (k x)) := by
  intro x y s eq
  apply recover
  rw [(keep s).pass_restrict (quiet x),(keep s).pass_restrict (quiet y), restricted hk eq]

theorem quotient {m q : (Fin 3 → X) → Poly J} (hm : Located m) (hq : Located q)
    (unit : ∀ x, (q x).part (J).quiet = 1) : Located (fun x => total (m x) (q x)) := by
  intro x y s eq
  apply recover
  have changeInv (b : Poly J) (blank : b.part (J).quiet = 1) :
      (keep s).restriction (inverseMass b) = inverseMass ((keep s).restriction b) := by
    unfold inverseMass
    rw [(keep s).pass_restrict, map_neg,(keep s).connected_restrict blank]
    rw [Poly.part_neg,connected_quiet blank,neg_zero]
  change (keep s).restriction (m x * inverseMass (q x)) = (keep s).restriction (m y * inverseMass (q y))
  rw [map_mul,map_mul,changeInv _ (unit x),changeInv _ (unit y),
    restricted hm eq,restricted hq eq]

variable {G : Gauge} (R : Run G) (A : Group R.family 6)
local notation "d" => WilsonOriginalThermometerPalette.levels
local notation "V" => R.family.path.levels

theorem physical {f : Extraction.Order} {H : (Bel R.family.book).Hierarchy}
    (checked : A.station.checked f H A.horizon)
    (unit : ∀ t : Fin 7, A.change t ((Bel R.family.book).unit t) = (Bel R.family.book).unit t) :
    ∀ᶠ z : UVIndex in f.fuse, Located (WilsonThermometerFiniteConnectedCells.measured R A z) := by
  filter_upwards [WilsonThermometerCourseIntake.subwords R A checked unit] with z word
  intro x y s eq
  change R.family.omega z.1 z.2 (WilsonThermometerCourseIntake.placed R A z s.val x) =
    R.family.omega z.1 z.2 (WilsonThermometerCourseIntake.placed R A z s.val y)
  apply congrArg
  funext U
  rw [word,word]
  exact Finset.prod_congr rfl fun i hi => by rw [eq i hi]

def filed {N per : ℕ} (caps : Fin 3 → ℕ) (w : ∀ i, d i < caps i)
    (phase : Fin 3 → ℂ →ₗ[ℝ] ℝ) (j : ℕ) (n : Side) (lift : Site (R.family.side N per) → Cover)
    (test : Case caps) (sense : ∀ s : (J).Mode, (s.val → Site (R.family.side N per)) → PChart G n →ₗ[ℝ] ℂ)
    (x : Fin 3 → Site (R.family.side N per)) : Poly J :=
  let seed := WilsonNeutralNominatedFiniteTable.top R A N per caps w phase
  Poly.inject fun s => sense s (fun i => x i) (finiteRead test s.val n
    (Gears V R.metals.O d d N N j seed (lift ∘ x) s.val))

/-- The named fitted top and its complete nonbare finite recurrence have the
same occupied-site law at every dated finite reading. A field-dependent
functional on the retained sites may be tested before the ordinary pass. -/
theorem nominated (simple : G.Simple) {N per j : ℕ} (live : j ≤ N)
    (caps : Fin 3 → ℕ) (w : ∀ i, d i < caps i) (phase : Fin 3 → ℂ →ₗ[ℝ] ℝ)
    (n : Side) (lift : Site (R.family.side N per) → Cover) (test : Case caps)
    (sense : ∀ s : (J).Mode, (s.val → Site (R.family.side N per)) → PChart G n →ₗ[ℝ] ℂ) :
    let k := filed R A caps w phase j n lift test sense
    Located k ∧ (∀ x, (k x).part (J).quiet = 0) ∧ Located (fun x => Poly.pass (k x)) := by
  let seed := WilsonNeutralNominatedFiniteTable.top R A N per caps w phase
  have health : Wellness d (Gears V R.metals.O d d N N j seed) :=
    Cog V R.metals.O le_rfl seed (WilsonNeutralNominatedFiniteTable.healthy R A N per caps w phase)
      simple R.alloy.B.ratio live
  let k := filed R A caps w phase j n lift test sense
  have good : Located k := by
    intro x y s eq
    have coords : (fun i : s.val => x i) = (fun i : s.val => y i) := funext fun i => eq _ i.property
    change sense s _ (finiteRead test s.val n (Gears V R.metals.O d d N N j seed (lift ∘ x) s.val)) = _
    have same : Gears V R.metals.O d d N N j seed (lift ∘ x) s.val =
        Gears V R.metals.O d d N N j seed (lift ∘ y) s.val :=
      health.filial (lift ∘ x) (lift ∘ y) s.val (fun i hi => congrArg lift (eq i hi))
    rw [coords,same]
    rfl
  have zero (x) : (k x).part (J).quiet = 0 := by
    change sense (J).quiet _ (finiteRead test ∅ n (Gears V R.metals.O d d N N j seed (lift ∘ x) ∅)) = 0
    rw [health.quiet' _,map_zero,map_zero]
  exact ⟨good,zero,exponential good zero⟩

end YM.Integration.WilsonThermometerNominatedDeletion
