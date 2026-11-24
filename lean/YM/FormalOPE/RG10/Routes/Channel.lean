import YM.FormalOPE.RG10.Routes.Accounts
import YM.FormalOPE.RG10.Balance

/-!
# Normalized increments on polynomial channels

Use flat Taylor frame after square completion and mean shift data. Coordinates:

* `I` is the fine gauge slice/leg family of the step, termwise joint Gaussian at `q` over J
(using the *same realization on every marker*);
* `B` is the coarse field family;
* `Q` below needs supplied post-square log weight from the joint (normalized block) Wilson germ,
removing the common scalar and Gaussian factors ONLY, with zero constant, already reexpressed in
chosen power-series coupling. In particular must include the **integrand** soft denominator/Haar
vertices whenever there; exact matches here on setting J(kernel)=1 because we include every such
term as log weight. No mask. No conditioning shortcut;
* `transfer` multiplies that complete relative weight at fixed y, takes the full formal Gaussian
mean and divides by the full unmarked conditional denominator. Coarse fields still at their
positions; no value/capture/readout projection.

Analytic notion suggested by `billed` requires estimates on these SAmplitudes; use only when
provided. This is a specialization of the same coefficient system as `FlatFeed`; it is NOT
specifying RG08's vacuum supplies, estimating an IR theory, choosing the actual Family or
changing it in one location.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route
open Function Finset MvPolynomial PowerSeries Joins Joins.Gauss
open scoped BigOperators Classical
open Multi.Vacuum.Gauss
variable {I J B : Type} [Fintype J]

abbrev Channel (I : Type) := PowerSeries (Packet I)
variable (p : Channel I) (x : I→ℂ)

def run (x : I → ℂ) : Channel I →+* RG10.Series := PowerSeries.map (MvPolynomial.aeval x : Packet I →ₐ[ℂ] ℂ)
lemma run_charge (n : ℕ) : PowerSeries.coeff n (run x p) = MvPolynomial.aeval x (PowerSeries.coeff n p) := by rw [run, PowerSeries.coeff_map]; rfl
lemma all_conf {p q : Packet I} (h : ∀ x:I→ℂ,MvPolynomial.aeval x p = MvPolynomial.aeval x q) : p=q := MvPolynomial.funext (by simpa using h)
lemma runs_determine {A B : Channel I} (h : ∀ x:I→ℂ,run x A=run x B) : A=B := by
  apply PowerSeries.ext; intro n; apply all_conf; intro x; rw [← run_charge,←run_charge,h x]
-- commutes with literal scalars
lemma run_const (f : Series) : run x (PowerSeries.map (MvPolynomial.C (σ:=I) (R:=ℂ)) f) = f := by
  apply PowerSeries.ext; intro n; rw [run_charge, PowerSeries.coeff_map]; exact aeval_C _ _

def advance (p : Channel I) : Channel I := PowerSeries.mk fun n => ∑ i∈ range (n+1), (i.factorial:ℂ)⁻¹ • PowerSeries.coeff n (p^i)
lemma advanced : run x (advance p) = expTaylor (run x p) := by
  apply PowerSeries.ext; intro k; rw [run_charge,expTaylor,advance, coeff_mk,coeff_mk]; rw [map_sum];
  refine Finset.sum_congr rfl fun i _ => ?_; rw [AlgHom.map_smul_of_tower _ _ _,← run_charge,map_pow]; rfl
lemma advanced_start : PowerSeries.coeff 0 (advance p)=1 := by simp [advance]
namespace Bulk
variable (q : I → Row J)
local notation "F" => standardFeed J
local notation "H" => hall J

def mean : hall J →ₗ[ℂ] ℂ where
  toFun f := (F).mean f.val
  map_add' a b := FlatFeed.mean_add (accepted J a.val a.property) (accepted J b.val b.property)
  map_smul' c b := FlatFeed.mean_smul F c b.val

def hand (p : Packet (I⊕B)) : Packet B := ∑ i∈p.support, mean (leaking q (glyph (fine i))) • MvPolynomial.monomial (coarse i) (MvPolynomial.coeff i p)

variable (y : B→ℂ) (r : (Channel (I⊕B)))
lemma hand_eq (p:Packet (I⊕B)) : aeval y (hand q p) = mean (study q y p) := by
  unfold hand; nth_rw 3 [p.as_sum]
  rw [map_sum, map_sum, map_sum]
  refine sum_congr rfl fun i _ => ?_; rw [map_smul,rolled, map_smul]; exact mul_comm ..

def move (P : (Channel (I⊕B))) : Channel B := mk fun i => hand q (PowerSeries.coeff i P)

def water (q : I → Row J) (y : B → ℂ) : (Channel (I⊕B)) →+* Kernel (Unit × Row J) :=
  RingHom.pi (fun (i : Unit × Row J)=> run (Sum.elim (alongFine q i.2) y))

lemma watered (x) (k) : row k (water q y r) x= (study q y (PowerSeries.coeff k r)).val x :=
  (run_charge r (Sum.elim (alongFine q x.2) y) k).trans (study_apply ..).symm
lemma sufficient : (F).Funded (water q y r) := fun n => by rw [_root_.funext (fun x=>watered q y r x n)]; exact accepted J _ (study q y _).property
lemma report : run y (move q r)= (F).average (water q y r) := by
  apply PowerSeries.ext; intro n; rw [run_charge,FlatFeed.average_coeff,move, coeff_mk,hand_eq];
  rw [_root_.funext (fun x=>watered q y r x n)]; rfl
variable (Q : (Channel (I⊕B))) (hz : PowerSeries.coeff 0 Q = 0)

def intake : Vertices (Unit× Row J) where
  J := 1
  V := water q y Q
  J0 := by apply _root_.funext; intro x; change PowerSeries.coeff 0 (1:Series)=1; simp
  V0 := by apply _root_.funext; intro x; rw [watered, hz,map_zero]; rfl
lemma heaviness : (intake q y Q hz).weight = water q y (advance Q) := by
  funext x; change expTaylor _ * 1= _; rw [mul_one]; exact (advanced Q (Sum.elim (alongFine q x.2) y)).symm

def income := move q (advance Q)
def transfer := move q (advance Q * r) * PowerSeries.invOfUnit (income q Q) 1
lemma accounting : PowerSeries.coeff 0 (income q Q)= 1 := by
  unfold income move; rw [PowerSeries.coeff_mk,advanced_start]; apply all_conf; intro y; rw [hand_eq,map_one (MvPolynomial.aeval (R:=ℂ) y), map_one]; exact (F).mean_one
lemma enters : run y (income q Q) = (F).den (intake q y Q hz) := by rw [income,report,FlatFeed.den, ← heaviness q y Q hz]
lemma inverse : run y (PowerSeries.invOfUnit (income q Q) 1) = ((F).den (intake q y Q hz))⁻¹ := by
  apply PowerSeries.eq_inv_iff_mul_eq_one (by rw [← coeff_zero_eq_constantCoeff_apply,FlatFeed.den0]; exact one_ne_zero)|>.2
  rw [← enters, ← map_mul, invOfUnit_mul, map_one]; exact (coeff_zero_eq_constantCoeff_apply _).symm.trans (accounting ..)

lemma unfolds_step : run y (transfer q r Q) = (F).step (intake q y Q hz) (water q y r) := by
  rw [transfer,map_mul,inverse,FlatFeed.step,report,map_mul,heaviness]
lemma paid_step : (F).Funded ((intake q y Q hz).weight * water q y r) := by rw [heaviness,← map_mul]; exact sufficient q y _
include hz in
lemma transfer_add (r' : (Channel (I⊕B))) : transfer q (r+r') Q=transfer q r Q+transfer q r' Q := by
  apply runs_determine; intro y; rw [map_add]; simp_rw [unfolds_step q y _ Q hz]; rw [map_add,FlatFeed.step_add (paid_step q y r Q hz) (paid_step q y r' Q hz)]
-- `transfer` applies only with zero constant vertex proof, later map will carry that

end Bulk
end YM.FormalOPE.RG10.Route
