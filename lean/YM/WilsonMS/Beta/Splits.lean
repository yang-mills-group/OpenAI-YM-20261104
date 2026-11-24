import YM.WilsonMS.Beta.Flash
/-!
# Koszul accounting of shell operations (bulk convention, conserving)
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
open Complex (I)
open scoped Topology ContDiff BigOperators

variable {G : Gauge}

abbrev LaneHeat (G : Gauge) :=
  Flux (BH G) QP ℂ
local notation "γ" => field parity

private lemma pot_grade (l : List (Lane4 G)) :
    degree (field parity) l = (if fieldDim ghostNo l % 2 = 1 then true else false) := by
  induction l with
  | nil => simp [fieldDim]
  | cons i w ih =>
    rw [degree_cons, field_cons, ih]
    rcases i with ⟨⟨⟨_ | i, _ | _⟩, u⟩, p⟩
    all_goals
      unfold ghostNo ghostChannel field parity Landau.p
      dsimp only
      split_ifs <;>
        first
        | rfl
        | omega

abbrev HitM (K : LaneHeat G) (F : Law G) (l r : Legs (Lane4 G)) :=
  attaches parity K (Cubic G) F l r

lemma law_S (r : ℝ) : Reverse (HeatLine G r) parity :=
  reverse_one _ (L_rev r) (fun _ => rfl)

lemma law_V (t : ℝ) : Reverse (Ribbon G t) parity := by
  intro i j q
  simp only [log_line, Pi.smul_apply, law_S (G := G) (exp t)]
  rw [Complex.real_smul, Complex.real_smul, mul_left_comm]

variable {T P : Law G} {K : LaneHeat G}

lemma swap_funding {l v : Legs (Lane4 G)} (hp : net l + net v = 0) (h : Reverse K parity)
    (hx : Solid true P 0) (hs : Solid true T 0) :
    attaches parity K P T v l = cross (degree γ v) (degree γ l) * attaches parity K T P l v := by
  rw [convertR h, convertR h, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw (occs := .pos [1]) [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold radius
  dsimp only
  rw [h j i (net v)]
  have hv : (-net v) = net l := by rw [add_eq_zero_iff_eq_neg.mp hp]
  have ht : (-net l) = net v := by rw [add_eq_zero_iff_eq_neg.mp hp, neg_neg]
  rw [hv, ht, hv]
  let q := (j, net l)
  let x := (i, net v)
  have hV : Course true (q :: v) := fun _ => by
    rw [net_cons]
    exact hp
  have hv' : Course true (x :: l) := fun _ => by
    rw [net_cons]
    exact (add_comm _ _).trans hp
  by_cases hL : P (q :: v) = 0
  · rw [show P ((j, net l) :: v) = _ from hL]
    ring
  by_cases hP : T (x :: l) = 0
  · rw [show T ((i, net v) :: l) = _ from hP]
    ring
  have he (w : Legs (Lane4 G)) (i : Lane4 G) (F : Law G) (hF : Solid true F 0)
    (H : Course true (i :: w)) (ht : F (i :: w) ≠ 0) : degree γ w = parity i.1 := by
    have hu : degree γ (i :: w) = false := by
      rw [pot_grade,
        show fieldDim ghostNo (i :: w) = 0 from
          (by
            by_contra hh
            exact ht (hF.ghost _ H hh)),
        if_neg (by decide)]
    cases hi : degree γ w <;> cases hp : parity i.1 <;>
      simp only [degree_cons, hi, show field parity i = _ from hp] at hu
    all_goals
      first
      | rfl
      | contradiction
  rw [he v q P hx hV hL, he l x T hs hv' hP]
  change 2 * (_ * K i j _) * (cross _ _ * _) * _ = cross _ _ * _
  simp only [x, q]
  cases hi : parity i <;> cases hj : parity j <;> simp <;> ring

lemma swap_tree (hp : Reverse K parity) (hx : Solid true P 0) (hs : Solid true T 0)
    (w : List (Lane4 G)) (he : net w = 0) : tree parity K P T w = tree parity K T P w := by
  unfold tree
  rw [Motif.swap]
  apply scatter_congr
  intro u v hv
  rw [swap_funding ((split_net hv).trans he) hp hx hs, ← mul_assoc,
    cross_comm (degree γ v) (degree γ u), cross_cross, one_mul]

lemma hit_only (hp : Reverse K parity) (u v : Legs (Lane4 G)) (t : u.length ≠ 2) : HitM K T u v = 0 := by
  rw [HitM, convertR hp]
  exact
    Finset.sum_eq_zero fun i _ =>
      Finset.sum_eq_zero fun j _ => by
        unfold radius
        dsimp only
        rw [none_cub (_ :: u)
            (by
              simp
              omega)]
        ring

variable (i j k l m : Lane4 G)
local notation "Q(" i "," j ")" => (cross (γ i) (γ j) : ℂ)

lemma grant_four (hp : Reverse K parity) :
    tree parity K (Cubic G) T [i, j, k, l] =
      HitM K T [i, j] [k, l] + Q(j,k) * HitM K T [i, k] [j, l] +
              Q(j,l) * Q(k,l) * HitM K T [i, l] [j, k] +
            Q(i,j) * Q(i,k) * HitM K T [j, k] [i, l] +
          Q(i,j) * Q(i,l) * Q(k,l) * HitM K T [j, l] [i, k] +
        Q(i,k) * Q(i,l) * Q(j,k) * Q(j,l) * HitM K T [k, l] [i, j] := by
  unfold tree
  simp only [scatter_cons, scatter_nil]
  have h u v (he : u.length ≠ 2) : attaches parity K (Cubic G) T u v = 0 := hit_only hp u v he
  rw [h [i, j, k, l] [] (by simp), h [] [i, j, k, l] (by simp), h [i, j, l] _ (by simp),
    h [j, k, l] _ (by simp), h [i, k, l] _ (by simp), h [i, j, k] _ (by simp), h [i] _ (by simp),
    h [j] _ (by simp), h [k] _ (by simp), h [l] _ (by simp)]
  simp_rw [degree_cons, degree_nil, cross_right, cross_false', mul_one]
  unfold HitM
  ring

lemma book_exchange (hp : Reverse K parity) (h : net [i, j, k, l] = 0) :
    Exchange K [i, j, k, l] =
      2 *
        (HitM K (Cubic G) [i, j] [k, l] + Q(j,k) * HitM K (Cubic G) [i, k] [j, l] +
          Q(j,l) * Q(k,l) * HitM K (Cubic G) [i, l] [j, k]) := by
  have ht := Crown G |>.solid
  change Solid true (Cubic G) 0 at ht
  simp only [net_cons, show net ([] : Legs (Lane4 G)) = 0 from rfl, add_zero] at h
  rw [Exchange, grant_four i j k l hp]
  have he (a b : List (Lane4 G)) (he : net b + net a = 0) : HitM K (Cubic G) a b = _ :=
    swap_funding he hp ht ht
  rw [he [j, k] _
      (by
        simp [net]
        rw [← h]
        abel),
    he [j, l] _
      (by
        simp [net]
        rw [← h]
        abel),
    he [k, l] _
      (by
        simp [net]
        rw [← h]
        abel)]
  cases hi : γ i <;> cases hj : γ j <;> cases hk : γ k <;> cases hl : γ l <;>
    simp only [degree_cons, hi, hj, hk, hl, degree_nil]
  all_goals
    norm_num [cross]
    unfold HitM
    ring

lemma grant_five (hp : Reverse K parity) :
    tree parity K (Cubic G) T [i, j, k, l, m] =
      HitM K T [i, j] [k, l, m] + Q(j,k) * HitM K T [i, k] [j, l, m] +
                      Q(j,l) * Q(k,l) * HitM K T [i, l] [j, k, m] +
                    Q(j,m) * Q(k,m) * Q(l,m) * HitM K T [i, m] [j, k, l] +
                  Q(i,j) * Q(i,k) * HitM K T [j, k] [i, l, m] +
                Q(i,j) * Q(i,l) * Q(k,l) * HitM K T [j, l] [i, k, m] +
              Q(i,j) * Q(i,m) * Q(k,m) * Q(l,m) * HitM K T [j, m] [i, k, l] +
            Q(i,k) * Q(i,l) * Q(j,k) * Q(j,l) * HitM K T [k, l] [i, j, m] +
          Q(i,k) * Q(i,m) * Q(j,k) * Q(j,m) * Q(l,m) * HitM K T [k, m] [i, j, l] +
        Q(i,l) * Q(i,m) * Q(j,l) * Q(j,m) * Q(k,l) * Q(k,m) * HitM K T [l, m] [i, j, k] := by
  unfold tree
  simp only [scatter_cons, scatter_nil]
  have h u v (he : u.length ≠ 2) : attaches parity K (Cubic G) T u v = 0 := hit_only hp u v he
  rw [h [i, j, k, l, m] [] (by simp)]
  rw [h [i, j, k, l] [m] (by simp), h [i, j, k, m] [l] (by simp), h [i, j, l, m] [k] (by simp),
    h [i, k, l, m] [j] (by simp), h [j, k, l, m] [i] (by simp)]
  rw [h [i, j, k] [l, m] (by simp), h [i, j, l] [k, m] (by simp), h [i, j, m] [k, l] (by simp),
    h [i, k, l] [j, m] (by simp), h [i, k, m] [j, l] (by simp), h [i, l, m] [j, k] (by simp),
    h [j, k, l] [i, m] (by simp), h [j, k, m] [i, l] (by simp), h [j, l, m] [i, k] (by simp),
    h [k, l, m] [i, j] (by simp)]
  rw [h [i] [j, k, l, m] (by simp), h [j] [i, k, l, m] (by simp), h [k] [i, j, l, m] (by simp),
    h [l] [i, j, k, m] (by simp), h [m] [i, j, k, l] (by simp)]
  rw [h [] [i, j, k, l, m] (by simp)]
  simp_rw [degree_cons, degree_nil, cross_right, cross_false', mul_one]
  unfold HitM
  ring
end YM.WilsonMS.BetaValue
