import YM.Integration.WilsonNeutralCopiedAngularJet
import YM.WilsonCoeffUV.Marked.Bounds.Output
import YM.WilsonCoeffUV.Product.Report.Post

/-! Enroll the bare numerical fields, with their original source normalization,
as independent finite marked inputs. The fired scalar is frozen at birth. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonNeutralCopiedProgram
open Lattice Wilson Labels RG Source PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open WilsonCoeffUV.Soil WilsonCoeffUV.Bank WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel.Mark
open WilsonNeutralCopiedField
open scoped BigOperators Classical
variable {G : Gauge} (R : Run G) {d D : ℕ}
local notation "F" => R.family.labels.level d
local notation "T" => R.family.localSection d

/-- Real or imaginary numerical source coefficient after the native `herald`
has divided out the leading field power. -/
def fee (N per : ℕ) (x : R.family.label d) (phase : ℂ →ₗ[ℝ] ℝ) (g : ℝ)
    (j : (F).Index) : ℝ := phase (coefficients R N per x j) * g ^ ((F).grades j).2

def submitted (N per : ℕ) (x : R.family.label d) (phase : ℂ →ₗ[ℝ] ℝ) (g : ℝ) : Verse F :=
  fun i => if i = point F (sheet F i) then PowerSeries.C (fee R N per x phase g (sheet F i)) else 0

private theorem stem_real (a : ℝ) (Y : TowerS G D) :
    Stem (PowerSeries.C a) Y = a • Y := by
  apply Prod.ext
  · exact funext fun n => purePayment (Y.1 n) a
  · exact purePayment _ _

theorem filed (N per : ℕ) (x : R.family.label d) (phase : ℂ →ₗ[ℝ] ℝ) (g : ℝ)
    (Y : Island F D) :
    Shrine Y (submitted R N per x phase g) = ∑ j, fee R N per x phase g j • vein Y (point F j) := by
  let e : (F).Index ↪ Alma F := ⟨point F, fun _ _ eq => congrArg (sheet F) eq⟩
  let fn (i : Alma F) := Stem (submitted R N per x phase g i) (vein Y i)
  have outside (i : Alma F) (hi : i ∉ Finset.univ.map e) : fn i = 0 := by
    have h : i ≠ point F (sheet F i) := fun h => hi
      (Finset.mem_map.mpr ⟨sheet F i, Finset.mem_univ _, h.symm⟩)
    change Stem (if i = point F (sheet F i) then _ else 0) _ = 0
    rw [if_neg h, ← (map_zero (PowerSeries.C (R:=ℝ))), stem_real, zero_smul]
  calc Shrine Y (submitted R N per x phase g) = ∑ i, fn i := rfl
    _ = ∑ i ∈ Finset.univ.map e, fn i :=
      (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => outside i hi)).symm
    _ = _ := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro j _
      change Stem (if point F j = point F j then _ else 0) _ = _
      rw [if_pos rfl, stem_real]
      rfl

/-- The deployed numerical row pays exactly the same retained coefficient as
the full raw angular field on the same side. -/
theorem priced (w : d < D) (N per : ℕ) (x : R.family.label d) (phase : ℂ →ₗ[ℝ] ℝ)
    (g : ℝ) (n : Side) (j : (F).Index) (k : ℕ) :
    (g^k * fee R N per x phase g j) • PowerSeries.coeff k
      (flash (jot (brow F (point F 0) D) ((Peaks R.family.path.levels R.metals.O T w N N).1 n (point F j)))) =
    (g^(k+((F).grades j).2) * phase (coefficients R N per x j)) •
      PowerSeries.coeff (k+((F).grades j).2) (jet (Plies T j n)) := by
  have h := congrArg (PowerSeries.coeff (k+((F).grades j).2))
    (WilsonNeutralCopiedAngularJet.one R w N n j)
  unfold WilsonNeutralCopiedAngularJet.reading at h
  rw [PowerSeries.coeff_X_pow_mul] at h
  rw [← h, fee, pow_add]
  congr 1
  ring

abbrev deck {ι : Type} (dims caps : ι → ℕ) (w : ∀ i, dims i < caps i) (i : ι) :=
  BayV (primes G) (dims i) (caps i) (w i)

/-- At birth the inverse transfer spans zero dates. The literal independent
marked program receives these same submitted fields at their individual sites. -/
theorem birth {ι : Type} [DecidableEq ι] (dims caps : ι → ℕ) (w : ∀ i, dims i < caps i)
    (N per : ℕ) (x : ∀ i, R.family.label (dims i)) (phase : ι → ℂ →ₗ[ℝ] ℝ)
    (g : ℝ) (z : ι → Cover) :
    let Q := deck (G:=G) dims caps w
    let v := fun i => submitted R N per (x i) (phase i) g
    let A := R.family.path.levels
    let L := R.metals.O
    (∀ i, coatA A L N N Q v z {i} =
       cn caps i (∑ j, fee R N per (x i) (phase i) g j • vein
         (Peaks A L (R.family.localSection (dims i)) (w i) N N) (point (R.family.labels.level (dims i)) j)) (z i)) ∧
      (∀ J, J.card ≠ 1 → coatA A L N N Q v z J = 0) := by
  intro Q v A L
  constructor
  · intro i
    rw [coatLeaf]
    have eq : centralL A L N N N (Q i) (v i) =
        Shrine (Peaks A L (R.family.localSection (dims i)) (w i) N N) (v i) := by
      unfold centralL polarP
      rw [Nat.sub_self]
      simp only [steep, relativeC, leeB, bindingS, steepen, Matrix.one_mulVec]
      exact congrArg (Shrine (Peaks A L (R.family.localSection (dims i)) (w i) N N))
        (funext fun j => Bank.reel_one ((v i) j))
    rw [eq]
    exact congrArg (fun H => cn caps i H (z i)) (filed R N per (x i) (phase i) g _)
  · exact fun J h => coatLazy A L N N Q v z J h

end YM.Integration.WilsonNeutralCopiedProgram

