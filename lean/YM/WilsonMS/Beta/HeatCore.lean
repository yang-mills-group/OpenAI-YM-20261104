import YM.WilsonMS.Beta.HeatLimit
/-!
# Leading two interactions at integral scale

Keep the whole `Archive` naming and UV subtraction values. Top cubic
rank-three pieces have no regularization dependence in this prescription;
not assuming their value at small q to implement that statement. For order-
two rank-four can have the UV explicit contact values.
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
variable {G : Gauge} {b : Bool} {B : Local.Physical.Deck G} {M : Booked B}
variable (F : MS_Data G M)
variable (x y t : ℝ)

abbrev Ribbon (G : Gauge) (t : ℝ) :=
  (spaceD G).meter t

abbrev HeatLine (G : Gauge) (r : ℝ) :=
  LegsK (A := G.ColorIndex) (id : Momentum Axis → Momentum Axis) r

lemma log_line : Ribbon G t = exp t • HeatLine G (exp t) := by
  funext i j p
  unfold Ribbon spaceD zD HeatLine LegsK
  simp only [Landau.choir, Pi.smul_apply]
  split
  · exact (brushed _ _ _ _).symm.trans (Complex.real_smul ..).symm
  simp

lemma line_zero (i j : BH G) : HeatLine G t i j 0 = 0 := by
  rcases i with ⟨⟨_ | a, _ | _⟩, i⟩ <;> rcases j with ⟨⟨_ | b, _ | _⟩, j⟩ <;>
    simp [HeatLine, LegsK, Landau.choir, L0, Momentum.sq, precision, delta]

lemma ribbon_nil (i j : BH G) : Ribbon G t i j 0 = 0 := by simp [log_line, line_zero]

abbrev Reach (F : MS_Data G M) (n : ℕ) (x t : ℝ) :=
  Archive 4 F.bulk n (x, t)

abbrev Cubic (G : Gauge) : Law G :=
  Motif.pulseX G 1 0

lemma dim_cub : Book.rank 3 (Cubic G) :=
  R_action G 1 0

lemma none_cub (w : Legs (Lane4 G)) (hp : w.length ≠ 3) : Cubic G w = 0 :=
  dim_cub w
    (by
      rw [mod_int]
      omega)

lemma cubic_reach (hG : G.Simple) (w : Legs (Lane4 G)) (h : net w = 0) :
    Reach F 1 x t w = Cubic G w := by
  by_cases he : w.length = 3
  · apply sub_eq_zero.mp
    exact
      HB (r := 3) F.bulkOK (Halo.invest G 1) (fun i => (Halo.fund_one G i).up) (s := t) (y := x) 0 w
        (by omega)
  rw [none_cub w he]
  obtain hv : pays 3 (Reach F 1 x t) := action_archive F 1 (x, t)
  by_cases ht : Allows 3 w.length
  swap
  · exact hv w ht
  obtain hh : List.length w = 1 := by
    obtain ⟨a, ha⟩ := ht
    omega
  obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp hh
  rcases i with ⟨⟨a, u⟩, z⟩
  refine Landau.single hG (p := fun i => Reach F 1 x t [qnote a i z]) ?_ u
  exact fun g i => ((archive_disc F).master.trueC 1 (x, t)).color [qnote a i z] (fun _ => h) g

abbrev Exchange (K : Flux (BH G) QP ℂ) : Law G :=
  tree parity K (Cubic G) (Cubic G)

theorem force_two (g : G.Simple) (w : List (Lane4 G)) (hp : net w = 0) :
    ledgerR F 2 (x, t) w =
      cycle (Ribbon G t) (covMeasure Axis) (Reach F 2 x t) w + (2 : ℂ)⁻¹ * Exchange (Ribbon G t) w := by
  unfold ledgerR Domain.recu Domain.using_tree
  rw [show Domain.paths 2 1 = { 1 } from ?_, Finset.sum_singleton]
  swap
  · ext i
    simp [Domain.paths]
  change (_ : ℂ) + ((2 : ℂ)⁻¹ * tree parity _ (Reach F 1 x t) (Reach F 1 x t) w) = _
  apply congr_arg₂ (· + ·) rfl
  exact
    congr_arg ((2 : ℂ)⁻¹ * ·) (agrees_tree _ _ _ _ (cubic_reach F x t g) (cubic_reach F x t g) w hp)

theorem force_four (g : G.Simple) (w : List (Lane4 G)) (he : net w = 0) (h : w.length = 4) :
    ledgerR F 2 (x, t) w = (2 : ℂ)⁻¹ * Exchange (Ribbon G t) w := by
  rw [force_two F x t g _ he, show cycle _ _ _ w = 0 from ?_, zero_add]
  unfold cycle
  simp only [at_trc]
  simp_rw [show ∀ i j : BH G, ∀ q : QP, Reach F 2 x t ((i, q) :: (j, -q) :: w) = 0 from fun i j q =>
      action_archive F 2 _ _
        (fun t => by
          have he := t.smaller
          simp [h] at he),
    mul_zero, Finset.sum_const_zero]
  simp

lemma Exchange_scale (c : ℝ) (p : Flux (BH G) QP ℂ) : Exchange (c • p) = c • Exchange p :=
  lineT (c : ℂ)

def primitive (w : List (Lane4 G)) (v : ℝ) :=
  (2 : ℂ)⁻¹ * (∫ r in 0..v, Exchange (HeatLine G r) w)

lemma arc_cont (w : List (Lane4 G)) : Continuous (fun v : ℝ => Exchange (HeatLine G v) w) := by
  let L (v : ℝ) := HeatLine G v
  have hp (i j : BH G) (p : QP) : Continuous fun v : ℝ => L v i j p := by
    rcases i with ⟨⟨_ | a, _ | _⟩, i⟩ <;> rcases j with ⟨⟨_ | b, _ | _⟩, j⟩ <;>
        simp only [L, HeatLine, LegsK, Landau.choir, id_eq, L0] <;>
      (split_ifs <;>
          first
          | exact continuous_const
          | ( unfold brush
              fun_prop))
  let N := Shared (Lane4 G) ℂ
  have he (j : Legs (Lane4 G)) (V : ℝ → N) (hx : ∀ w z, Continuous fun s : ℝ => V s w z) :
    Continuous fun s => scatter (field parity) j (V s) := by
    induction j generalizing V with
    | nil => exact hx [] []
    | cons i w ih =>
      simp only [scatter_cons]
      apply ih
      intro v z
      exact (hx ..).add (continuous_const.mul (hx ..))
  apply he w
  intro v z
  unfold attaches
  dsimp only
  apply continuous_finsetSum
  intro i hi
  refine
    continuous_finsetSum _
      (fun j _ => Continuous.add ((hp _ _ _).mul continuous_const) ((hp _ _ _).mul continuous_const))

lemma deriv_r (w : List (Lane4 G)) (r : ℝ) :
    HasDerivAt (primitive w) ((2 : ℂ)⁻¹ * Exchange (HeatLine G r) w) r :=
  (hfun (arc_cont w) r).const_mul _

theorem tree_equation (g : G.Simple) (w : List (Lane4 G)) (h : w.length = 4) (he : net w = 0) :
    Reach F 2 x t w = (if crown w = 4 then Reach F 2 x t (apex w) else 0) + primitive w (exp t) := by
  have ht : 4 ≤ crown w := by
    obtain ht := length_pay w
    rw [h] at ht
    exact ht
  let T (v : ℝ) := Reach F 2 x v w - primitive w (exp v)
  let K (v : ℝ) := Reach F 2 x v (apex w)
  have hp (v : ℝ) : T v = T 0 := constancy (fun v => ?_) v
  rotate_left
  · obtain H := η F x v w (by decide : 0 < (2 : ℕ)) (fun _ => he) (by omega)
    obtain hx :
      HasDerivAt (fun v : ℝ => primitive w (exp v)) ((2 : ℂ)⁻¹ * Exchange (Ribbon G v) w) v := by
      convert ((deriv_r w (exp v)).scomp v (Real.hasDerivAt_exp v)) using 1 <;> try rfl
      rw [log_line, Exchange_scale, Pi.smul_apply, Complex.real_smul, Complex.real_smul,
        mul_left_comm]
    convert! H.sub hx using 1
    rw [force_four F x v g w he h, sub_self]
  have he' (r : ℝ) : K r = K t := by
    have hq (v : ℝ) : K v = K 0 := constancy (fun v : ℝ => ?_) v
    rotate_left
    · let y := apex w
      have hx i (ht : i ∈ apex w) : i.2 = 0 := by
        unfold apex at ht
        rw [ray_go] at ht
        obtain ⟨i, hp, rfl⟩ := List.mem_map.mp ht
        exact zero_smul ..
      have hm : net y = 0 := by
        exact
          List.sum_eq_zero
            (fun _ hi => by
              obtain ⟨i, h', rfl⟩ := List.mem_map.mp hi
              exact hx i h')
      obtain ht :=
        η F x v y (by decide : 0 < (2 : ℕ)) (fun _ => hm)
          (by
            change 0 < List.length y
            rw [show List.length y = 4 from (fullness w).trans h]
            decide)
      rw [force_four F x v g _ hm ((fullness w).trans h), Exchange, tree_spike _ hx (ribbon_nil v),
        mul_zero] at ht
      exact ht
    exact (hq r).trans (hq t).symm
  obtain hh := ((deriv_r w 0).continuousAt.tendsto.comp tendsto_exp_atBot)
  rw [show primitive w 0 = 0 from (by simp [primitive])] at hh
  apply sub_eq_iff_eq_add.mp
  change T t = _
  by_cases hz : crown w = 4
  · rw [hp, if_pos hz]
    obtain hv := UV_zero_patch F x w 2 hz.symm
    have hx : Tendsto T atBot (𝓝 (K t)) := by
      convert! ((hh.neg.add hv).add_const (K t)) using 1
      · ext1 v
        rw [← he' v]
        unfold T K
        unfold Reach
        abel
      simp
    rw [funext hp] at hx
    exact tendsto_nhds_unique tendsto_const_nhds hx
  rw [hp, if_neg hz]
  have H := (UV_boundary (n := 2) F x w (lt_of_le_of_ne ht (Ne.symm hz))).sub hh
  rw [sub_zero] at H
  change Tendsto T _ _ at H
  rw [funext hp] at H
  exact tendsto_nhds_unique tendsto_const_nhds H
end YM.WilsonMS.BetaValue
