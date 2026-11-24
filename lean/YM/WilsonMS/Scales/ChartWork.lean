import YM.WilsonMS.XSpace.ExactBReg
import YM.XSpace.Terrain
/-!
# Formal frame actions on point-wise kernels

Same laws as the tested versions, include `Checks` translation to tests. No
Schwartz contact claims.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.FrameConj
open Function Set Filter MeasureTheory Real Finset
open XSpace XSpace.Normalize XSpace.Expense XSpace.Cirrus XSpace.TestBudget XSpace.Structure1
open Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Menus MS.Theater MS.Land MS.Book MS.Book.Program MS.Book.Convolve
open Fiscal BMenu Rider Reservoir VisitH Sea Fray
open PowerSeries (constantCoeff coeff mk)
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d n j k : ℕ}
local notation "BΨ" => Ensure.deck G
local notation "𝕄" => XSpace.Mesh
local notation "Eₖ" => Dime G d

abbrev Octave (G : Gauge) (d n : ℕ) :=
  T (Point G d n)
section laws
variable {F : Octave G d n} {R Q S : Guard G d} {c : Cn}

def pivot (R : Guard G d) (F : Octave G d n) : Octave G d n := fun j =>
  ∑ a ∈ Normalize.tally j n, (F (a none)).compLinearMap fun i => coeff (a (some i)) R

lemma pivot_cost (p : Fin n → Sec G d) :
    pivot R F j p = ∑ a ∈ Normalize.tally j n, F (a none) (pulseU a R p) := by
  unfold pivot
  rw [_root_.sum_apply]
  rfl

def RawPoint (F : Octave G d n) (p : Fin n → Sec G d) : Cn :=
  mk fun i => F i p

private lemma money (U : Point G d n) (p : Fin n → Sec G d) :
    U p = ∑ z : Fin n → Dime G d, U (fun i => dime G d (z i)) * ∏ i, (dime G d).repr (p i) (z i) := by
  let B := dime G d
  have hx := U.map_sum (fun i (j : Dime G d) => B.repr (p i) j • B j)
  simp_rw [B.sum_repr] at hx
  rw [hx]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [U.map_smul_univ (m := fun i => B (v i)), smul_eq_mul, mul_comm]

lemma grab_point (R : Guard G d) (F : Octave G d n) (p : Fin n → Sec G d) :
    RawPoint (pivot R F) p =
      ∑ z : Fin n → Dime G d,
        RawPoint F (fun i => dime G d (z i)) * ∏ i, Normalize.tax R (p i) (z i) := by
  have he (f : PowerSeries ℂ) (g : Fin n → PowerSeries ℂ) :
    f * ∏ i, g i = ∏ i : Option (Fin n), Option.elim i f g :=
    (Fintype.prod_option (fun i : Option (Fin n) => Option.elim i f g)).symm
  apply PowerSeries.ext
  intro i
  simp only [RawPoint, he, map_sum, PowerSeries.coeff_prod, PowerSeries.coeff_mk]
  rw [pivot_cost, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [money]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.prod_option]
  simp only [Option.elim, PowerSeries.coeff_mk, Normalize.tax]

lemma byRanks {P Q : Octave G d n} (h : ∀ p, RawPoint P p = RawPoint Q p) : P = Q := by
  funext j
  ext1 p
  obtain hp := congr_arg (coeff j) (h p)
  simpa only [RawPoint, PowerSeries.coeff_mk] using hp

lemma point_times (F : Octave G d n) (Q R : Guard G d) : pivot Q (pivot R F) = pivot (R * Q) F := by
  apply byRanks
  intro p
  rw [grab_point, grab_point]
  simp_rw [grab_point, Normalize.taxes, Fintype.prod_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.prod_mul_distrib, mul_assoc]

lemma bookCost (S : Cn) (F : Octave G d n) (p : Fin n → Sec G d) (k : ℕ) :
    substitute S F k p = substitute S (fun t => F t p) k := by
  simp_rw [rules, _root_.sum_apply, _root_.smul_apply]

lemma readMove (hx : Rooted c) (P : Octave G d n) (p : Fin n → Sec G d) :
    RawPoint (Program.substitute c P) p = Coupling.composeS c (RawPoint P p) := by
  apply PowerSeries.ext
  intro i
  rw [show
      coeff i (Coupling.composeS c (RawPoint P p)) = substitute c (Coupling.read (RawPoint P p)) i
      from (congr_fun (Coupling.explicit hx (RawPoint P p)) i).symm]
  conv_lhs => unfold RawPoint; rw [PowerSeries.coeff_mk, bookCost]
  rw [show Coupling.read (RawPoint P p) = (fun t => P t p) from
      funext fun i => PowerSeries.coeff_mk ..]

lemma pointMove (hx : Rooted c) (P : Guard G d) (F : Octave G d n) :
    substitute c (pivot P F) = pivot (coupon c P) (substitute c F) := by
  apply byRanks
  intro p
  rw [readMove hx, grab_point, grab_point]
  let L :=
    PowerSeries.substAlgHom (R := ℂ)
      (PowerSeries.HasSubst.of_constantCoeff_zero (Coupling.const_coupling (S := ℂ) hx))
  simp_rw [Sea.coupon_paid hx, readMove hx,
    show ∀ p : PowerSeries ℂ, Coupling.composeS c p = L p from fun p => by
      unfold Coupling.composeS L
      rw [PowerSeries.coe_substAlgHom],
    map_sum, map_mul, map_prod]
end laws
section kernel
variable {n : ℕ}

def FundsK (F : Points n → Octave G d n) (P : Reports G d) :=
  ∀ (i : ℕ) (p : Fin n → Sec G d),
    ContinuousOn (fun x => F x i p) (conf n) ∧ ∀ t, P i n t p = t.applyTo (fun x => F x i p)

lemma pivotFund {F : Points n → Octave G d n} {P : Reports G d} (h : FundsK F P) (V : Guard G d) :
    FundsK (fun x => pivot V (F x)) (realm V P) := by
  intro i p
  simp_rw [pivot_cost]
  refine ⟨continuousOn_finsetSum _ (fun i hi => (h _ _).1), fun t => ?_⟩
  rw [really]
  simp_rw [(h _ _).2, Test.applyTo, Finset.mul_sum,
    integral_finsetSum _ (fun _ _ => t.smearing (h _ _).1)]

lemma FundSwim {F : Points n → Octave G d n} {P : Reports G d} (h : FundsK F P) (v : Cn) :
    FundsK (fun x => substitute v (F x)) (substitute v P) := by
  intro i p
  simp_rw [bookCost, rules]
  simp only [Finset.sum_apply, LinearMap.sum_apply, Pi.smul_apply, LinearMap.smul_apply,
    _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  refine ⟨continuousOn_finsetSum _ (fun j _ => continuousOn_const.mul (h _ _).1), fun t => ?_⟩
  rw [Test.applyTo]
  simp_rw [Finset.mul_sum,
    show ∀ x j, t x * (cut v j i * F x j p) = cut v j i * (t x * F x j p) from fun _ _ =>
      mul_left_comm ..,
    integral_finsetSum _ (fun i _ => (t.smearing (h i p).1).const_mul _), integral_const_mul,
    (h _ _).2]
  rfl
end kernel
end YM.WilsonMS.FrameConj
