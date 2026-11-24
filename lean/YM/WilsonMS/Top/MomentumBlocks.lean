import YM.WilsonMS.Top.PositionBlock

/-! # Momentum blocks of the ordinary, pre-image term in MS.Master -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Position
open Function Finset Filter Set Matrix Complex Lattice
open MS MS.Orbit MS.Orbit.Cog MS.Koszul MS.Plane MS.Bare MS.Native
open MS.Book MS.Cylinder MS.Landau MS.Latch MS.City MS.Swirl MS.Swirl.Near MS.Tone
open MS.Momentum
open scoped Topology

variable (G : Gauge) (n : Side)
local notation "Nm" => SiteField G n
local notation "Qm" => GaugeField G n
local notation "WA" => FFT.forward (Ax G) n
local notation "WC" => FFT.forward G.ColorIndex n

abbrev wi (p : Site n) :=
  wave (Coord p)

abbrev muq (p : Site n) : ℂ :=
  (Momentum.sq (wi n p) : ℂ)

abbrev midPhase (p : QP) (i : Axis) : ℂ :=
  bill p ((1 / 2 : ℝ) • Tone.embed (step i))
local notation "ν" => scaleZ n
local notation "Λ" => brightness n

def CA : Matrix (SiteField G n) (SiteField G n) ℂ := fun i j =>
  Chill (mat n (FinalK G)) (aa G n i) (aa G n j)

def LK : Matrix (GaugeField G n) (SiteField G n) ℂ := fun i j =>
  -(Chill (mat n (FinalK G)) (cc G n i) (ak G n j))

lemma mid_inv (i : Axis) (p : QP) : midPhase p i * midPhase (-p) i = 1 := by
  unfold midPhase
  rw [opp, mul_inv_cancel₀ (nonz _ _)]

lemma mu_zero : muq n 0 = 0 := by
  rw [muq, wi, ξ_zero]
  simp [Momentum.sq, wave, Momentum.theta]

lemma wave_gap (p : Site n) (h : p ≠ 0) : muq n p ≠ 0 := by
  intro hv
  obtain ⟨i, hi⟩ := Bloch.step_picks p h
  have he : Momentum.sq (wave (Coord p)) = 0 := ofReal_injective hv
  have hz := Near.NoWave (wave (Coord p)) he
  have hZ := Tone.Frame.triangle i (-Coord p)
  rw [neg_neg, Tone.Frame.wave_neg, hz, neg_zero] at hZ
  apply hi
  have ht : Tone.bill (Coord p) (Tone.embed (step i)) = 1 := by
    rw [show (-(Complex.I * ↑((0 : QP) i))) = 0 by simp] at hZ
    exact sub_eq_zero.mp ((mul_eq_zero.mp hZ).resolve_left (Tone.nonz _ _))
  rwa [Tone.rights, Orbit.dual_cell, wrap_step] at ht

lemma A_matrix (p : Site n) (i j : Axis) (k l : G.ColorIndex) :
    CA G n ((i, k), p) ((j, l), -p) =
      if k = l then
        ν * midPhase (Coord p) i * midPhase (-Coord p) j * ((precision i j (wi n p) : ℝ) : ℂ) /
          (muq n p) ^ 2
      else 0 := by
  rw [CA]
  change Chill _ (atomA G _, p) (atomA G _, -p) = _
  rw [Near.ChillK]
  unfold Bass Landau.choir
  split
  next h =>
    rw [if_pos (show k = l from h)]
    change ν * (midPhase _ _ * midPhase _ _ * (↑(precision i j _ / _) : ℂ)) = _
    unfold muq wi
    push_cast
    ring
  next h => rw [if_neg (show k ≠ l from h), mul_zero, mul_zero]

lemma L_matrix (p : Site n) (i : Axis) (k l : G.ColorIndex) :
    LK G n (k, p) ((i, l), -p) =
      if k = l then -(ν * midPhase (-Coord p) i * (Complex.I * ↑(wi n p i)) / muq n p) else 0 := by
  rw [LK]
  change -Chill _ (atomC G _, p) (atomK G _, -p) = _
  rw [Near.ChillK]
  unfold Bass Landau.choir
  split
  next
    h =>
    rw [if_pos (show k = l from h), show flag (atomC G k) (Coord p) = 1 from Tone.right0 (Coord p)]
    change -(ν * (1 * midPhase _ _ * (Complex.I * ↑(((wave _ _) / _) : ℝ)))) = _
    unfold muq wi
    push_cast
    ring
  next h => rw [if_neg (show k ≠ l from h), mul_zero, mul_zero, neg_zero]

lemma AF_off (p q : Site n) (x y : Ax G) (h : q ≠ -p) : CA G n (x, p) (y, q) = 0 :=
  chillOff (atomA G x) (atomA G y) p q h

lemma LF_off (p q : Site n) (x : G.ColorIndex) (y : Ax G) (h : q ≠ -p) : LK G n (x, p) (y, q) = 0 :=
  Eq.trans (congr_arg Neg.neg (chillOff (atomC G x) (atomK G y) p q h)) neg_zero

lemma H_matrix (p : Site n) (i j : Axis) (k l : G.ColorIndex) :
    angularP G n ((i, k), -p) ((j, l), p) =
      if k = l then
        Λ * midPhase (Coord p) i * midPhase (-Coord p) j * ((precision i j (wi n p) : ℝ) : ℂ)
      else 0 := by
  rw [HHF]
  change -flatH G n [(atomA G _, -p), (atomA G _, p)] = _
  rw [Near.Neg_S, Near.oriented]
  unfold Landau.choir
  split
  next h =>
    rw [if_pos (show k = l from h)]
    simp only [lace, neg_neg]
    change -(Λ * (midPhase _ _ * midPhase _ _ * (-(precision i j (wi n p) : ℂ)))) = _
    ring
  next h => rw [if_neg (show k ≠ l from h), mul_zero, mul_zero, neg_zero]

lemma D_matrix (p : Site n) (i : Axis) (k l : G.ColorIndex) :
    angularD G n ((i, k), -p) (l, p) =
      if k = l then Λ * midPhase (Coord p) i * (Complex.I * ↑(wi n p i)) else 0 := by
  rw [DDF]
  change flatH G n [(atomK G _, -p), (atomC G _, p)] = _
  rw [Near.Neg_S, Near.oriented]
  unfold Landau.choir
  split
  next
    h =>
    rw [if_pos (show k = l from h), show lace (atomC G l, Coord p) = 1 from Tone.right0 (-Coord p)]
    simp only [mul_one, lace, neg_neg]
    change Λ * (midPhase _ _ * (Complex.I * ↑(wi n p i))) = _
    ring
  next h => rw [if_neg (show k ≠ l from h), mul_zero, mul_zero]

lemma HF_off (p q : Site n) (x y : Ax G) (h : q ≠ p) : angularP G n (x, -p) (y, q) = 0 := by
  rw [HHF,
    show flatH G n [aa G n (x, -p), aa G n (y, q)] = 0 from S_hold (atomA G x) (atomA G y) p q h,
    neg_zero]

lemma DF_off (p q : Site n) (x : Ax G) (y) (h : q ≠ p) : angularD G n (x, -p) (y, q) = 0 := by
  rw [DDF]
  exact S_hold (atomK G x) (atomC G y) p q h
end YM.WilsonMS.Position
