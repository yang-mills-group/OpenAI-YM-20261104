import YM.WilsonMS.Beta.Tethered
/-!
# The AA/CU marginal costs have a simple contact part

Both actual shell derivatives. An unknown contact from order-two vertices is
retained, but on the tested jets it won't transmit. Remaining answers can be
expressed via the explicit real shell integrals. Uses this MS calculation,
not the `HardAnswer`/Alba route.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BetaValue
open Function Filter Set Finset MeasureTheory Metric
open LoopRank Lattice MS Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect
  Native
open Book Convolve City Logarithm Signal Landau.Detect.Mark Wind High Knobs
open LogTime LogTime.IntervalFamily Outlook Land Arc Wire Rock Path Oceans Plum Alps Garment Color
  Pearl
open Arts Motif Halo
open HeatPapers RG FormalOPE.RG10.MultiGauge
open Complex (I)
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {B : Local.Physical.Deck G} {M : Land.Booked B} (F : Land.MS_Data G M)
variable (x t : ℝ) (p q : QP) (w : List (Lane4 G))
local notation "R" => Reach F
local notation "Κ" => HeatLine G 1

lemma part_menu (b : BH G) (a : BH G) : Integrable (Κ b a) mplane := by
  have hx (i : Axis) : Integrable (fun q : QP => City.brush 1 q * (q.sq * q i)) mplane :=
    brush_funded _ (Sheet.heat_sq.mul (Sheet.read i))
  have ht (i j : Axis) : Integrable (fun q : QP => City.brush 1 q * precision i j q) mplane :=
    brush_funded _ (Sheet.face i j)
  unfold HeatLine LegsK Landau.choir
  by_cases h : b.2 = a.2
  swap
  · simp_rw [if_neg h]
    exact integrable_zero ..
  simp_rw [if_pos h]
  rcases b with ⟨⟨_ | b, _ | _⟩, m⟩ <;> rcases a with ⟨⟨_ | a, _ | _⟩, n⟩ <;>
      simp only [L0, id_eq] <;>
    first
    | exact integrable_zero ..
    | exact Complex.ofRealCLM.integrable_comp (ht b a)
    | exact Integrable.const_mul (Complex.ofRealCLM.integrable_comp (hx _)) _

def TabP (w : List (Lane4 G)) : ℂ :=
  if crown w = 4 then Reach F 2 x 0 (apex w) else 0

lemma tab_eq (w : List (Lane4 G)) (u : ℝ) : TabP F x (sail (ray w) u) = TabP F x w := by
  unfold TabP crown apex
  rw [sail_dim, ray_dim, show sail (ray (sail (ray w) u)) 0 = sail (ray w) 0 from ?_]
  simp only [ray_go, List.map_map, Function.comp_def, zero_smul]

lemma tab_stave : trc Κ p (TabP F x) w = trc Κ p (TabP F x) (apex w) := by
  simp_rw [at_trc]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  unfold TabP
  rw [show crown ((a, p) :: (b, -p) :: apex w) = crown ((a, p) :: (b, -p) :: w) from ?_,
    show apex ((a, p) :: (b, -p) :: apex w) = apex ((a, p) :: (b, -p) :: w) from ?_]
  · unfold apex
    simp only [ray_go, List.map_cons, List.map_map, Function.comp_def, zero_smul]
  unfold crown
  simp only [field_cons, show fieldDim wfield (apex w) = _ from dimension0 w]

lemma tab_paid : Integrable (fun q : QP => trc Κ q (TabP F x) w) mplane := by
  simp_rw [at_trc]
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  have hp (x' : QP) : TabP F x ((i, x') :: (j, -x') :: w) = TabP F x ((i, 0) :: (j, 0) :: w) := by
    unfold TabP apex
    simp only [crown, field_cons, ray_go, List.map_cons, zero_smul]
  simp_rw [hp]
  exact (part_menu i j).mul_const _

def Medal (w : List (Lane4 G)) (r : ℝ) : ℂ :=
  trc (HeatLine G 1) p ((2 : ℂ)⁻¹ • (Exchange (HeatLine G r))) w

lemma first_only (K : LaneHeat G) (h : Reverse K parity) (hp : w.length = 2) : Exchange K w = 0 := by
  unfold Exchange tree
  rw [scatter_congr _ w _ (fun _ _ => (0 : ℂ)) ?_]
  exact map_zero (allocate ..)
  intro i j hi
  rw [convertR h]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  unfold radius
  dsimp only
  obtain he := split_length hi
  by_cases hh : i.length = 2
  · rw [none_cub (_ :: j)
        (by
          simp
          omega)]
    ring
  rw [none_cub (_ :: i)
      (by
        simp
        omega)]
  ring

lemma stamp_at (g : G.Simple) (hw : net w = 0) (hl : w.length = 2) :
    trc (Ribbon G 0) p (Reach F 2 x 0) w = trc Κ p (TabP F x) w + ∫ r in 0..(1 : ℝ), Medal p w r := by
  let μ (a b : BH G) := (a, p) :: (b, -p) :: w
  have h (a b : BH G) : R 2 x 0 (μ a b) = TabP F x (μ a b) + primitive (μ a b) 1 := by
    rw [tree_equation F x 0 g _
        (by
          unfold μ
          rw [List.length_cons, List.length_cons, hl])
        (by
          unfold μ
          simp [hw]),
      exp_zero]
    rfl
  unfold Medal
  rw [log_line, Real.exp_zero, one_smul]
  simp_rw [at_trc, Pi.smul_apply, smul_eq_mul]
  let Z (a b : BH G) (r : ℝ) := (Κ a b p * ((2 : ℂ)⁻¹ * Exchange (HeatLine G r) (μ a b)))
  have hp (a b : BH G) : IntervalIntegrable (Z a b) volume 0 1 :=
    (((arc_cont (μ a b)).intervalIntegrable ..).const_mul (2 : ℂ)⁻¹).const_mul (Κ a b p)
  have hx (t : BH G) : IntervalIntegrable (fun r => ∑ a : BH G, Z t a r) volume 0 1 := by
    exact
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
        (integrable_finsetSum _ fun i _ =>
          (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (hp t i))
  change (∑ i : BH G, ∑ j : BH G, _) = _ + ∫ r in 0..(1 : ℝ), ∑ a : BH G, ∑ b : BH G, Z a b r
  rw [intervalIntegral.integral_finsetSum (fun i _ => hx i)]
  simp_rw [intervalIntegral.integral_finsetSum (fun i _ => hp _ i), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Reach F 2 x 0 ((i, p) :: (j, -p) :: w) = _ from h i j, mul_add]
  unfold primitive Z
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

def seaCap :=
  ∫ q : QP, trc Κ q (TabP F x) w ∂mplane

lemma computesF (w : List (Lane4 G)) (hw : w.length = 2) (he : net w = 0) (g : G.Simple) (c c' : ℂ)
    (p : QP) (Y : QP → ℝ) (ht : Sheet Y) (Z : ℝ → QP → ℂ)
    (hZ : ∀ r q, Z r q = c * (Pill r p q * Y q : ℝ))
    (hP : ∀ q r, Medal q w r = c' * (Z r q + Z r (-q))) :
    ledgerR F 2 (x, 0) w = seaCap F x (apex w) + c' * (2 * c * ↑(∫ r in (0 : ℝ)..1, tune p Y r)) := by
  rw [force_two F x 0 g _ he, first_only w _ (law_V 0), mul_zero, add_zero]
  swap
  · exact hw
  unfold cycle
  simp_rw [stamp_at F x _ w g he hw, hP, intervalIntegral.integral_const_mul, tab_stave F x _ w]
  obtain h := paymentμ p Y ht Z c hZ
  rw [MeasureTheory.integral_add (tab_paid F x (apex w)) (h.2.const_mul _),
    MeasureTheory.integral_const_mul]
  congr 1
  rw [h.1]

lemma apexA (i : CI G) : apex (AA G i p) = AA G i 0 := by simp [apex, AA, W, qnote]

lemma apexC (i : CI G) : apex (CU G i p) = CU G i 0 := by simp [apex, CU, C, U, qnote]

def SpurA (t : ℝ) (q : QP) :=
  Musc (Kproj t) q

def SpurK (t : ℝ) (q : QP) :=
  2 * t * (q.sq + (q + Kproj t).sq) * precision 0 0 q

def period (F : ℝ → QP → ℝ) (p : ℝ) :=
  ∫ r in (0 : ℝ)..1, tune (Kproj p) (F p) r

lemma value_full (i : CI G) (g : G.Simple) :
    ledgerR F 2 (x, 0) (AA G i (t • Punit)) =
      seaCap F x (AA G i 0) + colorScore i * (2 * 1 * ↑(period SpurA t)) := by
  rw [computesF F x _ rfl (show net (AA G i (t • Punit)) = 0 from (by simp [AA, W, qnote, net])) g 1
      (colorScore i) (Kproj t) (SpurA t) (Sheet.turtle _) (fun u q => EAm u (Kproj t) q)
      (fun u q => by
        rw [one_mul, Am_real]
        rfl)
      (fun q r => paidAm i r _ q),
    apexA]
  rfl

lemma ghost_full (i : CI G) (g : G.Simple) :
    ledgerR F 2 (x, 0) (CU G i (t • Punit)) =
      seaCap F x (CU G i 0) + colorScore i * (2 * I * ↑(period SpurK t)) := by
  rw [computesF F x _ rfl (show net (CU G i (t • Punit)) = 0 from (by simp [CU, C, U, qnote, net])) g
      I (colorScore i) (Kproj t) (SpurK t) (HeatPapers.Sheet.flame t) (fun r q => Kleg r (Kproj t) q)
      (fun r q => k_real ..) (fun q r => paid_Km i r (Kproj t) q),
    apexC]
  rfl
end YM.WilsonMS.BetaValue
