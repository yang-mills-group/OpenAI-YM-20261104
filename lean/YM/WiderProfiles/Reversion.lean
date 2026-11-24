import YM.WiderProfiles.Layout
import YM.FVA2.Speed.Faith
/-!
# Through the actual coupling change

Compare `Speed/ Poll.Clock.Sure.reverse, Faith.Timeframe.payment`.
Slopes are under the stronger *uniformly bounded* price (use `Sharp` as
filed, including the constant-centred special case for the inverse). But
take `Bond` for comparing the two `Point` stories.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.WiderProfiles
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival Dframe Expense
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors MS.Theater PowerSeries
open Normalize.Fray Reg Reg.Pivot Reg.Point Reg.Unique CoverTest Photo Higher State Reg.Choice
open Speed Speed.Star Asymptotics Finset Speed.Clock Reg.Token Reg.Faith
open scoped Topology ContDiff BigOperators Classical

variable {n a d k : ℕ} {G : Gauge} {c D : ℝ}
local notation "ι" => Domain n a c D
local notation "ℓ" => along n a c D
abbrev Receipt (x y : ι → PowerSeries ℂ) : Prop :=
  ∀ k, Costing (fun i => coeff k (x i)) (fun i => coeff k (y i))

lemma reverse {x y z : Domain n a c D → PowerSeries ℂ} (q : PowerSeries ℂ)
    (hq : Rooted q) (ht : coeff 1 q ≠ 0)
    (hp : Speed.Clock.Sure (along n a c D) (fun i => grab i.val) z (fun _ => q))
    (hz : ∀ᶠ i in ℓ, Rooted (z i))
    (hh : Receipt (fun i => (x i).subst (z i)) (fun i => (y i).subst q)) : Receipt x y := by
  have h := stretch n a c D
  intro m; induction m using Nat.strong_induction_on with
  | h m ih =>
    let b := coeff m (q^m)
    have he : b ≠ 0 := by unfold b; rw [Token.stamp_n q hq]; exact pow_ne_zero _ ht
    have hv := Speed.Clock.Sure.pow h m hp m
    -- diagonal coefficients of z^m, q^m nonzero eventually, with inverse comparison
    let Z i := coeff m (z i ^ m)
    have hw : Fast ℓ (fun i => grab i.val) (fun i => (Z i)⁻¹) (fun i => b⁻¹) :=
      Fast.constant (w:=fun z : ℂ => z⁻¹) h (differentiableAt_id.inv he) hv.sails
    have hT : Costing (fun i => Token.tend (x i) (z i) m)
        (fun i => Token.tend (y i) q m) :=
      Bond.sum (fun i => le_max_right ..) _ _ _ (fun j hj =>
        Bond.mul (fun i => le_max_right ..) (ih j (Finset.mem_range.mp hj))
          (sharp_bond (Speed.Clock.Sure.pow h j hp m)))
    refine (Bond.mul (fun i => le_max_right ..) (Bond.sub (fun i => le_max_right ..) (hh m) hT)
      (sharp_bond (Sharp.above hw))).tee ?_ (Eventually.of_forall fun i => ?_)
    · filter_upwards [hz, (Fast.aims h _ hv.sails).eventually (eventually_ne_nhds he)] with i hi hi'
      rw [← div_eq_mul_inv]; exact Eq.symm (Token.meter (x i) hi m hi')
    dsimp only; rw [← div_eq_mul_inv]; exact Eq.symm (Token.meter (y i) hq m he)

variable (μ : ℝ) (Y : XSpace.Initialize G) {V : Normalize.Store G} (K : Rose.Pick V)
    (A : Prescription (Press.portDeck G)) {O : Booked (Press.portDeck G)} (S : MS_Data G O)
    (h : G.Simple) (hs : TaylorOKF S (Press.wickInput Y) A)
    (hr : Position.Favors.Horder A) (hu : Position.Ace.UnitP A)
include h hs hr hu
open Rose

theorem rate_bond (a : ℕ) (hc : 0 < c) (hD : 1 ≤ D) (k : ℕ) (p : Tags G d n) :
    Costing (fun i : Domain n a c D => Rose.measureₓ Y K d i.val k p)
      (fun i => Reg.Faith.rate μ K S d (familiar i.val) k p) := by
  let q := Reg.Choice.choice μ K S
  let P (i : Domain n a c D) := Point.story (measureₓ Y K d i.val) p
  let M (i : Domain n a c D) := Reg.Faith.Touch μ K S (familiar i.val) p
  let Q (i : Domain n a c D) := prospects μ Y K A i.val.F
  have ht := hearty μ Y K A S h hs hr hu
  have he (x : Points n) : (Reg.Faith.Touch μ K S x p).subst q = Point.story (State.wall μ V S d x) p := by
    unfold Reg.Faith.Touch q; rw [rate_era μ Y K A S h hs hr hu, moves _ _ ht.cost.own,
      subst_comp_subst_apply (licence _ ht.cost.own) (licence _ (proper μ K S)), ht.cost.left, X_subst]
  have hh : Receipt (fun i => (P i).subst (Q i)) (fun i => (M i).subst q) := by
    intro j
    let Z (i : Domain n a c D) := Point.story (substitute (reset μ A i.val.F) (Rose.cooked Y V d i.val)) p
    have hw : Receipt Z (fun i => Point.story (State.wall μ V S d (familiar i.val)) p) := by
      intro k; simp_rw [Z,Point.story,coeff_mk]; exact cooked_bond μ Y V A S h hs hc hD hr hu a k p
    refine Bond.tee (hw j) ?_ (Eventually.of_forall fun i => congr_arg _ (he (familiar i.val)).symm)
    filter_upwards [(tended n a c D).eventually (usable Y K h)] with i hi
    unfold Z P Q; rw [moves _ _ (share ..), recompose μ Y K A i.val p hi]
  have hp : Costing (fun i => coeff k (P i)) (fun i => coeff k (M i)) :=
    reverse q (proper μ K S) (by unfold q; rw [stance μ Y K A S h hs hr hu]; exact one_ne_zero)
      (fun j => Sharp.once (w:=fun i : Domain n a c D => grab i.val) (tended n a c D)
        (Speed.Clock.Detected.clocked μ Y K A S h hs hr hu j))
      (Eventually.of_forall (fun i => g0 μ Y K A _)) hh k
  simpa only [P,M,Reg.Faith.Touch,Point.story,coeff_mk] using hp
end YM.FVA2.WiderProfiles
