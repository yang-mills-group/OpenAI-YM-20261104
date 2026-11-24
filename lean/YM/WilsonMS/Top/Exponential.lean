import YM.WilsonMS.Top.TreePlane
import YM.WilsonMS.Top.Encode

/-! # Check the power-series exponents in bosonic specialization -/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Symbols
open Next.Rank.Normal Function Filter Set Finset
open MS MS.Koszul MS.Cylinder MS.Cylinder.Taylor MS.Book MS.Book.Convolve MS.Swirl MS.Orbit
  MS.Orbit.Cog
open MS.Puff MS.Puff.Engine MS.Puff.Actors MS.Puff.SplitP MS.Puff.Mom MS.Puff.Dynamics
open scoped Topology ContDiff

variable {I E : Type}

lemma zero_grade (F : Raw I ℂ) : rankLevel 0 F 0 = coin (F []) := by
  ext l
  cases l with
  | nil => exact enough [] rfl
  | cons i l =>
    exact
      strange _
        (by
          simp
          omega)

lemma all_even (F : Raw I ℂ) : Pure (plain I) false F := by
  have hh (l : List I) : degree (plain I) l = false := by
    induction l with
    | nil => rfl
    | cons i l ih =>
      rw [degree_cons, ih]
      rfl
  exact fun l h => (h (hh l)).elim

lemma constantClock (F : Raw I ℂ) :
    clock useN (Raw I ℂ) (rankLevel 0 F) = rankLevel 0 (Tick (fun _ => 1) F) := by
  ext1 n
  funext l
  by_cases ht : (l.length : ℤ) = (n : ℤ) + 0
  · have hh (l : List I) : Owed (fun _ : I => 1) l = (l.length : ℂ) := by
      induction l with
      | nil => simp [Owed]
      | cons i l ih =>
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        change (1 : ℂ) + Owed (fun _ => 1) l = _
        rw [ih, add_comm]
    unfold rankLevel
    rw [cloak, Pi.smul_apply, enough _ ht, enough _ ht]
    change (n : ℂ) * F l = _ * _
    rw [hh _, show l.length = n from (by omega)]
  unfold rankLevel
  rw [cloak, Pi.smul_apply, strange _ ht, strange _ ht, smul_zero]

lemma multiplies (F G : Raw I ℂ) :
    rankLevel 0 (product (plain I) F G) = (PermV (plain I)).core (rankLevel 0 F) (rankLevel 0 G) :=
  funext
    (fun n =>
      (pairLevel n (h := 0) (g := 0) (F := F) (H := G)
          (by
            intro l h
            omega)
          (by
            intro l h
            omega)).symm)

lemma exponentiates [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I] (B : I → E) (f : E → ℝ)
    (hf : germ f) (h : f 0 = 0) :
    exp0 (plain I) (rankLevel 0 (ink B f)) = rankLevel 0 (ink B (Real.exp ∘ f)) := by
  let p := plain I
  let g := Real.exp ∘ f
  have he : germ g := Real.contDiff_exp.contDiffAt.comp 0 hf
  let b : I → ℂ := fun _ => 1
  let X := ink B f
  let Y := ink B g
  let w := actor p
  let V := rankLevel 0 X
  let U := rankLevel 0 Y
  have hp (i : I) : p i = true → B i = 0 := fun H => Bool.noConfusion H
  have hy (i : I) : D i Y = product p (D i X) Y := by
    unfold Y X
    rw [inktip, inktip]
    rw [← ink_mul _ hp (germ_layer hf _) he, inkit (f' := layer (B i) f * g) B ?_]
    filter_upwards [hf.eventually (by simp)] with a ha
    dsimp only [Function.comp_apply, g, layer, Pi.mul_apply]
    unfold Function.comp
    rw [fderiv_exp (ha.differentiableAt (by simp))]
    simp [mul_comm]
  have hx : Tick b Y = product p (Tick b X) Y := by
    rw [overture b (ink_s _ hp he), overture b (ink_s _ hp hf)]
    unfold X Y g p at *
    simp only [hy, ← times_assoc, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  have hw : Happy useN V := by
    change rankLevel 0 (ink B f) 0 = 0
    rw [zero_grade, drip, h]
    ext l
    cases l <;> rfl
  refine tick_agree useN w (u := clock useN (Raw I ℂ) V) (tick0 ..) ?_ ?_ ?_
  · change w.Cheer useN V useN.origin = rankLevel 0 (ink B g) 0
    rw [Stencil.simple_E _ _ _ hw, zero_grade]
    simp only [drip, g, Function.comp_apply, h, Real.exp_zero, Complex.ofReal_one]
    rfl
  · exact (turn_clock useN w).idea (fun i _ => all_even (V i)) hw
  rw [constantClock, constantClock, show Tick _ Y = _ from hx]
  exact multiplies _ _

abbrev PS (I : Type) :=
  PowerSeries (poly I)

def turn (P : PS I) (n : ℕ) :=
  encode I (PowerSeries.coeff n P)

lemma turn_unit : turn (1 : PS I) = (PermV (plain I)).unit := by
  classical
  ext1 n
  change turn (1 : PS I) n = useN.refineV _ n
  unfold turn
  by_cases h : n = 0
  · subst n
    rw [refineV, if_pos (show 0 = useN.origin from rfl)]
    rw [PowerSeries.coeff_zero_one]
    change encode I 1 = coin 1
    simpa using (encode_const (I := I) 1)
  rw [PowerSeries.coeff_one, if_neg h, map_zero, refineV, if_neg (show n ≠ useN.origin from h)]

lemma turn_mul (P Q : PS I) : turn (P * Q) = (PermV (plain I)).core (turn P) (turn Q) := by
  funext n
  rw [turn, PowerSeries.coeff_mul, map_sum]
  exact Finset.sum_congr rfl fun i _ => encode_product ..

lemma turn_power (P : PS I) (n : ℕ) : turn (P ^ n) = (PermV (plain I)).power (turn P) n := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact turn_unit
  | succ n ih =>
    rw [pow_succ', turn_mul, ih]
    rfl
end YM.WilsonMS.Symbols

namespace YM.WilsonMS.Root
open XSpace XSpace.Bare Function Filter Set Finset Precision Lattice
open MS MS.Koszul MS.Cylinder MS.Cylinder.Taylor MS.Book MS.Book.Convolve MS.Swirl MS.Orbit
  MS.Orbit.Cog
open MS.Puff MS.Puff.Actors MS.Puff.SplitP MS.Puff.Mom
open Symbols
open scoped Topology ContDiff BigOperators

variable {P : Period} (T : P.Tree) (G : Gauge)
local notation "Yact" => PermV (plain (T.Key G))

def haarTerm (x : T.Field G) :=
  orbitLog G (plantL T G x)

lemma haar_terms (x : T.Field G) : haarTerm T G x = ∑ j : T.Free, Bare.Maurer.lac (x j) := by
  unfold haarTerm orbitLog
  classical
  have he :
    (∑ i : P.Link, MS.Bare.Maurer.lac (plantL T G x i)) =
      ∑ i ∈ Finset.univ.filter (fun i : P.Link => i ∉ T.edges), MS.Bare.Maurer.lac (plantL T G x i) := by
    symm
    refine Finset.sum_subset (subset_univ _) (fun i hi hv => ?_)
    rw [plant_apply, Period.Tree.prolong, dif_pos (show i ∈ T.edges from (by simpa using hv))]
    simp [MS.Bare.Maurer.lac, LocalH.spin_zero]
  rw [he]
  rw [Finset.sum_subtype _ (p := fun i => i ∉ T.edges) (by simp)]
  apply Finset.sum_congr rfl
  intro i _
  rw [plant_apply, Period.Tree.prolong_free]

lemma genuineJ : relative (G := G) T =ᶠ[𝓝 0] Real.exp ∘ haarTerm T G := by
  let W := chart G
  have hw := MS.Bare.Maurer.real_ratio (Bare.chart_ratio G)
  filter_upwards [eventually_all.mpr
      (fun e : T.Free =>
        (continuous_apply (A := fun _ : T.Free => G.Color) e |>.tendsto (0 : T.Field G)).eventually
          (hw.and (MS.Bare.Maurer.lives G)))] with
    u hu
  rw [Function.comp_apply, haar_terms, Real.exp_sum]
  unfold XSpace.Bare.relative
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact (hu i).1.trans (Real.exp_log (hu i).2).symm

lemma HAexp : turn (haar T G) = exp0 (plain _) (rankLevel 0 (ink (T.basis G) (haarTerm T G))) := by
  have hf : germ (haarTerm T G) :=
    ContDiffAt.comp (g := orbitLog G) (f := ⇑(plantL T G)) 0
      (by
        rw [map_zero]
        exact orbit_germ (P := P) G)
      (plantL T G).contDiff.contDiffAt
  have hp : haarTerm T G 0 = 0 := by
    unfold haarTerm
    simp [orbitLog, MS.Bare.Maurer.lac, LocalH.spin_zero]
  rw [exponentiates _ _ hf hp, ← inkit (T.basis G) (genuineJ T G)]
  ext1 n
  unfold haar turn Taylor.expandTaylor
  rw [PowerSeries.coeff_mk, encode_expansion (T.basis G) _ (XSpace.Bare.relative_smooth ..)]
  unfold rankLevel
  rw [add_zero]

lemma INTexp : turn (interactionExp T G) = exp0 (plain _) (turn (Bare.interaction T G)) := by
  ext1 n
  rw [turn, Bare.exponential_formula, map_sum]
  let M := PermV (plain (T.Key G))
  let V := Bare.interaction T G
  let X := turn V
  change _ = (M.cheers X n) n
  unfold cheers
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show
      algebraMap ℚ (Vertices T G) ((1 : ℚ) / (↑(i.factorial) : ℚ)) = MvPolynomial.C (Actors.phase i)
      from ?_,
    MvPolynomial.C_mul', map_smul]
  exact (congr_arg ((Actors.phase i) • ·) (congr_fun (turn_power V i) n))
  norm_num [Actors.phase]

lemma separates :
    sliceInteraction T G =
      rankLevel 0 (ink (T.basis G) (haarTerm T G)) + turn (Bare.interaction T G) := by
  ext1 n
  by_cases he : n = 0
  · subst n
    rw [Pi.add_apply, zero_grade]
    unfold haarTerm
    rw [drip, map_zero]
    simp [sliceInteraction, turn, Bare.interaction]
    rw [show orbitLog G (0 : LogSpace G P) = 0 from
        (by simp [orbitLog, MS.Bare.Maurer.lac, LocalH.spin_zero])]
    ext i
    cases i <;> rfl
  rw [Pi.add_apply, sliceInteraction, if_neg he, turn, Bare.interaction, PowerSeries.coeff_mk,
    if_neg he, map_neg, encode_expansion (T.basis G) _ (T.continuousJet G)]
  let f : T.Field G → ℝ := T.action
  rw [rankLevel, ← neg_one_smul ℝ f, ink_smul _ (T.continuousJet G), Complex.ofReal_neg,
    Complex.ofReal_one, neg_one_smul, map_neg, Nat.cast_add]
  exact add_comm ..

lemma SLdensity : turn (weight T G) = exp0 (plain _) (sliceInteraction T G) := by
  let U := rankLevel 0 (ink (T.basis G) (haarTerm T G))
  let Y := turn (Bare.interaction T G)
  let M := PermV (plain (T.Key G))
  rw [weight, turn_mul, HAexp, INTexp, separates]
  refine
    (cheer_a (M := actor (plain _)) (P := useN) (x := U) (y := Y) (fun i _ => all_even _)
        (fun i _ => all_even _) ?_ ?_).symm
  · change rankLevel 0 (ink (T.basis G) _) 0 = 0
    rw [zero_grade, drip]
    simp [haarTerm, orbitLog, MS.Bare.Maurer.lac, LocalH.spin_zero]
    ext i
    cases i <;> rfl
  change turn (Bare.interaction T G) 0 = 0
  simp [turn, Bare.interaction]
end YM.WilsonMS.Root
