import YM.Integration.AllOrderOPE
import YM.FormalOPE.RG10.Linear

/-!
Prepare the exact RG10 input for downstream coefficient identification.
Only the actual construction and its local-section valuation are needed;
no global Floral package or prescription-identification assertion is assumed.
Finite series-valued mixtures retain the original horizon of every term.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open Lattice Wilson PowerSeries RG06 RG06.WilsonCompiler
open FormalOPE.RG10 FormalOPE.RG10.InversionTop
open PertExtension PertExtension.Orb
open scoped BigOperators Classical

variable {G : Gauge} (C : Family G) (N p d : ℕ)

/-- Direct local-section valuation supplies the exact real source's lower
coefficient vanishing; no global construction package is needed here. -/
theorem wilsonIRSource_below_grade_of_pop
    (hV : Bid.pop (C.localSection d)) (x : Site (C.side N p))
    (i : (C.labels.level d).Index) (k : ℕ)
    (hk : k < ((C.labels.level d).grades i).2) :
    wilsonIRSource C N p d x i k = 0 := by
  have hz : PowerSeries.coeff k
      (physicalCoverFilm C N p d
        (Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i))) = 0 := by
    rw [physicalCoverFilm, Dict06.Actual.meet, (C.labels.level d).coords_basis,
      PowerSeries.coeff_C_mul, markTop_coeff_casing,
      Tokens.doesNotStart (C.localSection d) hV i k hk, mul_zero]
  rw [wilsonIRSource, physicalFilm_periodize, PowerSeries.coeff_map, hz, map_zero]
  have hr : realPolynomial (0 : MvPolynomial (LinkVar G (Per (C.side N p))) ℂ) = 0 := by
    ext m
    simp [realPolynomial_coeff]
  rw [hr, map_zero]

variable (hC : C.Makes)

def valuedOPEStamp (hV : Bid.pop (C.localSection d))
    (x : Site (C.side N p)) (i : (C.labels.level d).Index) :
    InversionTop.Stamp G (C.side N p) where
  stencil := physicalInversionObservable C N p d x i
  test := physicalInversion_pretest C N p d hC x i
  slots := ((C.labels.level d).grades i).2
  cleared k hk := by
    funext z
    rcases z with ⟨⟨⟩,u⟩
    unfold row
    rw [wilsonInversion_raw_source C N p d hC x i u]
    rw [wilsonIRSeries, PowerSeries.coeff_mk,
      wilsonIRSource_below_grade_of_pop C N p d hV x i k hk]
    simp

theorem valuedOPEStamp_factor (hV : Bid.pop (C.localSection d))
    (x : Site (C.side N p)) (i : (C.labels.level d).Index) :
    (valuedOPEStamp C N p d hC hV x i).couplingMark = actualOPEFactor C N p d x i := by
  funext z
  rcases z with ⟨⟨⟩,u⟩
  unfold InversionTop.Stamp.couplingMark valuedOPEStamp actualOPEFactor
  rw [wilsonInversion_raw_source C N p d hC x i u]

variable (hV : ∀ d, Bid.pop (C.localSection d))
    {I : Type} [Fintype I] {J : I → Type} [∀ i, Fintype (J i)]
    (degree : (i : I) → J i → ℕ)
    (positions : (i : I) → J i → Site (C.side N p))
    (basis : (i : I) → (j : J i) → (C.labels.level (degree i j)).Index)
    (weight : (i : I) → J i → FormalOPE.RG10.Series)

/-- An explicit finite formal-series mixture of original actual source
columns. All terms use the one common bare coupling variable. -/
def preparedOPEFactors : I → Kernel (Unit × Orb.Dir G (C.side N p)) :=
  FlatFeed.combined weight (fun i j =>
    actualOPEFactor C N p (degree i j) (positions i j) (basis i j))

include hC hV in
/-- Finite triangular or other explicit mixtures preserve integrability and
have the exact finite sum of original-regulator product expansions. This
prepares the LHS of the external identification; it asserts no MS equality. -/
theorem preparedOPE_products (hn : Even (C.side N p).val) :
    let A := preparedOPEFactors C N p degree positions basis weight
    let F := InversionTop.feed hn
    let W := InversionTop.vertices G (C.side N p)
    F.Funded (W.weight * ∏ i, A i) ∧
      F.step W (∏ i, A i) =
        ∑ choice : (i : I) → J i, (∏ i, weight i (choice i)) *
          lower (∑ i, ((C.labels.level (degree i (choice i))).grades (basis i (choice i))).2)
            (InversionTop.into (PowerSeries.mk (Orb.diag
              (Orb.restrictedO (∏ i,
                physicalInversionObservable C N p (degree i (choice i))
                  (positions i (choice i)) (basis i (choice i))))))) := by
  let S (i : I) (j : J i) := valuedOPEStamp C N p (degree i j) hC (hV (degree i j))
    (positions i j) (basis i j)
  have hf : (fun i j => (S i j).couplingMark) =
      (fun i j => actualOPEFactor C N p (degree i j) (positions i j) (basis i j)) := by
    funext i j
    exact valuedOPEStamp_factor C N p (degree i j) hC (hV (degree i j))
      (positions i j) (basis i j)
  have h := InversionTop.Stamp.combine_stamps hn weight S
  rw [hf] at h
  exact h

omit [Fintype I] in
include hC hV in
/-- The same preparation works on every finite subset. In particular, the
empty subset keeps the vacuum-normalized unit, while the individual term
horizons remain unchanged under restriction. -/
theorem preparedOPE_subsets (hn : Even (C.side N p).val) (t : Finset I) :
    let A := preparedOPEFactors C N p degree positions basis weight
    let F := InversionTop.feed hn
    let W := InversionTop.vertices G (C.side N p)
    F.Funded (W.weight * ∏ i ∈ t, A i) ∧
      F.ordinary W t A =
        ∑ choice : (i : ↥t) → J i.val, (∏ i : ↥t, weight i.val (choice i)) *
          lower (∑ i : ↥t,
            ((C.labels.level (degree i.val (choice i))).grades (basis i.val (choice i))).2)
            (InversionTop.into (PowerSeries.mk (Orb.diag
              (Orb.restrictedO (∏ i : ↥t,
                physicalInversionObservable C N p (degree i.val (choice i))
                  (positions i.val (choice i)) (basis i.val (choice i))))))) := by
  let S (i : I) (j : J i) := valuedOPEStamp C N p (degree i j) hC (hV (degree i j))
    (positions i j) (basis i j)
  have hf : (fun i j => (S i j).couplingMark) =
      (fun i j => actualOPEFactor C N p (degree i j) (positions i j) (basis i j)) := by
    funext i j
    exact valuedOPEStamp_factor C N p (degree i j) hC (hV (degree i j))
      (positions i j) (basis i j)
  have h := InversionTop.Stamp.combine_at hn weight S t
  rw [hf] at h
  exact h

end YM.Integration
