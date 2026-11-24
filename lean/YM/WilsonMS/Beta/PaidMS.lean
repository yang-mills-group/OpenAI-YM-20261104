import YM.WilsonMS.Beta.Hinge
/-!
# Three scale variations to be evaluated

On this exact prescription (paying the unmarked high-mode `Fixed`). Read the
corresponding Taylor jets in the MS calculation. Their log µ changes are the
log-length shell effects at the corresponding scale. Keep dependence on MS
input data explicit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BetaValue
open Function Filter Set Finset MeasureTheory Metric
open LoopRank Lattice MS
open Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect Native Native.Wilsonian
  Paint
open Book Convolve City Logarithm Program Signal
open Cylinder Lab Menus Lifting Landau.Detect.Mark Wind High Knobs Rider
open LogTime LogTime.IntervalFamily Outlook Land
open PowerSeries (coeff)
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {b : Bool} {X : Dec G} {T : Team} {B : Local.Physical.Deck G} {M : Booked B}
variable (F : MS_Data G M) (h : Valid T) (hp : PC G T X)
  (hc : Fixed (col X) (Archive 4 F.bulk) true 4 1)
variable (x y t : ℝ)

include h hp hc

lemma turn_A (i : G.ColorIndex) :
    torch 2 (Archive 4 F.bulk 2 (x, t) - Archive 4 F.bulk 2 (y, t)) (AA G i Punit) =
      -(2 * (Ax T x - Ax T y)) := by
  have varied_at (u v : ℝ) :
    X 2 x u (AA G i (v • Punit)) - X 2 y u (AA G i (v • Punit)) =
      -(2 * (Ax T x - Ax T y)) * (precision 1 1 (Momentum.wave (v • Punit)) : ℂ) :=
    (origin_square h hp x y u _ rfl).trans (varied_A h x y i _)
  refine
    read_delta F hp hc 2 (by decide) x y t (AA G i Punit)
      (fun _ => by simp [AA, Detect.W, net, qnote]) (by simp [AA]) 2 rfl _ (fun t => ?_)
  let f (u : ℝ) : ℂ := (precision 1 1 (Momentum.wave (u • Punit)) : ℂ)
  let w (u : ℝ) := AA G i (u • Punit)
  rw [torch_at]
  simp_rw [show ∀ u : ℝ, sail (ray (AA G i Punit)) u = w u from fun u => by
      simp [w, AA, Detect.W, qnote]]
  simp only [Pi.sub_apply, col]
  change reading 2 (fun u => (X 2 x _ (AA G i (u • Punit)) - X 2 y _ (AA G i (u • Punit)))) = _
  simp_rw [varied_at]
  rw [read_const, show reading 2 f = 1 from ?_, mul_one]
  convert (baseK Punit 1 1).home 2 (show (2 : ℤ) ≤ 2 from le_rfl) using 1
  rw [Mark.prec_at]
  norm_num

lemma turn_K (i : G.ColorIndex) :
    torch 1 (Archive 4 F.bulk 2 (x, t) - Archive 4 F.bulk 2 (y, t)) (CU G i Punit) =
      -(Cx T x - Cx T y - (Ax T x - Ax T y)) * Complex.I := by
  refine
    read_delta F hp hc 2 (by decide) x y t (CU G i Punit) (fun _ => by simp [CU, C, U, net, qnote])
      (by simp [CU]) 1 rfl _ (fun t => ?_)
  let a := -(Cx T x - Cx T y - (Ax T x - Ax T y)) * Complex.I
  let f (u : ℝ) : ℂ := (Momentum.wave (u • Punit) 0 : ℂ)
  let S := col X 2 (x, t) - col X 2 (y, t)
  rw [torch_at, show (fun u => S (sail (ray (CU G i Punit)) u)) = fun u => a * f u from ?_,
    read_const, show reading 1 f = 1 from ?_, mul_one]
  rotate_left
  · funext u
    unfold S
    rw [show sail (ray (CU G i Punit)) u = CU G i (u • Punit) from ?_, Pi.sub_apply]
    swap
    · simp [CU, C, U, qnote]
    rw [col, col, origin_square h hp _ _ _ _ rfl, varied_U h]
    unfold a f
    ring
  · convert (waveFormR Punit 0).home 1 (show (1 : ℤ) ≤ 1 from le_rfl) using 1
    norm_num [Punit]

lemma turn_S (a b c : G.ColorIndex) :
    torch 0 (Archive 4 F.bulk 3 (x, t) - Archive 4 F.bulk 3 (y, t)) (SCC G a b c) =
      (φC T x - φC T y + (Cx T x - Cx T y)) * (↑(LieColor a b c) : ℂ) := by
  refine
    read_delta F hp hc 3 (by decide) x y t (SCC G a b c) (fun _ => by simp [SCC, C, qnote, net])
      (by simp [SCC]) 0 rfl _ ?_
  intro t
  rw [torch_at]
  simp only [reading, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  rw [show sail (ray (SCC G a b c)) 0 = SCC G a b c from (by simp [SCC, C, qnote]), Pi.sub_apply]
  exact origin_SCC h hp x y (exp t) a b c

omit h hp hc

abbrev ledgerR (n : ℕ) : Reading G :=
  Domain.recu (spaceD G) 1 ((2 : ℂ)⁻¹) (Archive 4 F.bulk) (Archive 4 F.bulk) n

lemma logD (n : ℕ) (hn : 0 < n) (w : Legs (Lane4 G)) (hl : 0 < w.length) (hw : Course true w)
    (j : ℕ) :
    HasDerivAt (fun t => torch j (Archive 4 F.bulk n (x, t)) w) (torch j (ledgerR F n (x, t)) w) t := by
  have hv : Domain.Used true (ray w) := fun _ => by
    rw [ray_len]
    exact hl
  have ht := ((archive_disc F).master.road ℝ (ray w) n hn hv (ray_course hw)).2.2 x t 0 j
  simp_rw [torch_at, reading, iteratedDeriv]
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => ℝ) ℂ (fun _ => 1)
  exact (L.hasFDerivAt.comp_hasDerivAt _ ht).const_smul (Nat.factorial j : ℝ)⁻¹

lemma μ_rise (n : ℕ) (w : Legs (Lane4 G)) (j : ℕ) (H : fieldDim wfield w + j = 4) (hn : 0 < n)
    (hl : 0 < w.length) (ht : Course true w) :
    HasDerivAt (fun x => torch j (Archive 4 F.bulk n (x, 0)) w) (torch j (ledgerR F n (x, 0)) w) x := by
  obtain he := logD F x 0 n hn w hl ht j
  simp_rw [margin F x _ w j H] at he
  have hh (q : ℝ) (hp : q = x - x) :
    HasDerivAt (fun v => torch j (Archive 4 F.bulk n (x + v, 0)) w) (torch j (ledgerR F n (x, 0)) w)
      q := by
    rw [hp, sub_self]
    exact he
  convert!
    (hh (x - x) rfl |>.scomp (h := fun v : ℝ => v - x) x ((hasDerivAt_id' x).sub_const x)) using 1
  · ext
    simp [add_comm x]
  simp
end YM.WilsonMS.BetaValue
