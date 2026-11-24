import YM.XSpace.Playing
/-!
# Multi-maximal frames are power series on each test. Action coherently formal.

Why positioning removes power-divergent ambiguity at increasing orders, without
singular-error amplification from insertions: equality at mesh on position
precomposed arrays follows from honest formal action. Needed before comparison
through kbulk.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick PowerSeries
open Finset hiding mul_sum sum_mul
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d n l:ℕ}
def said (P : Reports G d) (t:Test n) (p: Fin n→ Sec G d): PowerSeries ℂ:= mk fun i=> P i n t p
abbrev Dime (G:Gauge) (d:ℕ):= Fin (Module.finrank ℂ (Sec G d))
def dime (G:Gauge) (d:ℕ) := Module.finBasis ℂ (Sec G d)
def tax (S:Guard G d) (p:Sec G d) (j:Dime G d): PowerSeries ℂ:= mk fun i=> (dime G d).repr (coeff i S p) j
private lemma spelled (P: MultilinearMap ℂ (fun _:Fin n=> Sec G d) ℂ) (p: Fin n→Sec G d):
    P p= ∑ z: Fin n→Dime G d, P (fun i=> dime G d (z i)) * ∏ i, (dime G d).repr (p i) (z i):=by
  let a:= dime G d; have h:= P.map_sum (fun i (j:Dime G d)=> a.repr (p i) j • a j); simp_rw [a.sum_repr] at h; conv_lhs=> rw [h]
  apply Finset.sum_congr rfl; intro i _; rw [P.map_smul_univ (m:=fun j=> a (i j)), smul_eq_mul, mul_comm]
private lemma productSp {f:PowerSeries ℂ} (g:Fin n→ PowerSeries ℂ): f * ∏ i,g i = ∏ i:Option (Fin n), (Option.elim i f g):=(Fintype.prod_option (fun i:Option (Fin n)=> Option.elim i f g)).symm
lemma talks (P: Reports G d) (S:Guard G d) (t:Test n) (p:Fin n→Sec G d):
    said (realm S P) t p=∑ z:Fin n→ Dime G d, said P t (fun i=> dime G d (z i))* ∏ i,tax S (p i) (z i):=by
  apply PowerSeries.ext; intro l; simp only [said, productSp, map_sum,coeff_prod, coeff_mk]; rw [really,sum_comm]; apply sum_congr rfl; intro x _; rw [spelled]; refine sum_congr rfl (fun i _=>?_); rw [Fintype.prod_option]; simp only [Option.elim, coeff_mk, tax]
set_option maxHeartbeats 500000 in
private lemma bill (n:ℕ) (P Q: Guard G d) (p:Sec G d): coeff n (P*Q) p=∑ i∈ Finset.antidiagonal n, coeff (R:=FieldEnd G d) i.1 P (coeff i.2 Q p):=by rw [coeff_mul n P Q]; exact LinearMap.sum_apply ..
private lemma taxBill (P': FieldEnd G d) (y: Sec G d) (j:Dime G d): (dime G d).repr (P' y) j=∑ i:Dime G d,(dime G d).repr (P' (dime G d i)) j*(dime G d).repr y i:=by
  conv_lhs=> rw [← (dime G d).sum_repr y, map_sum,map_sum];
  rw [Finsupp.finsetSum_apply]; apply sum_congr rfl; intro x _; simp [mul_comm]
lemma taxes (P Q:Guard G d) (p:Sec G d) (j:Dime G d): tax (P*Q) p j=∑ i:Dime G d,tax P (dime G d i) j*tax Q p i:=by
  refine PowerSeries.ext fun n=>?_
  simp only [tax,map_sum, coeff_mk, coeff_mul (R:=ℂ)]; rw [bill (G:=G),map_sum,Finsupp.finsetSum_apply, sum_comm]
  exact sum_congr rfl (fun _ _=> taxBill _ _ _) -- need order
lemma speaking (P: Reports G d) (X Y:Guard G d) (t:Test n) (p:Fin n→ Sec G d):
    said (realm X (realm Y P)) t p= said (realm (Y*X) P) t p:=by
  rw [talks,talks]; simp_rw [talks, taxes, Fintype.prod_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro v _; apply Finset.sum_congr rfl; intro a _; rw [Finset.prod_mul_distrib, mul_assoc]
theorem parlance (X Y: Guard G d) (R: Reports G d): realm X (realm Y R)=realm (Y*X) R:=by
  ext1 n; ext1 l; ext1 t; ext1 p; have hh:= congr_arg (coeff n) (speaking R X Y t p); simpa only [said,coeff_mk] using hh
private lemma tax_one (j:Dime G d) (p: Sec G d): tax 1 p j = C ((dime G d).repr p j) :=by
  apply PowerSeries.ext; intro n; rw [tax,coeff_mk,coeff_C,coeff_one]; split_ifs with h; · subst n; rfl
  simp
lemma sweet (R:Reports G d) (t:Test n) (p:Fin n→Sec G d): said (realm 1 R) t p=said R t p:=by
  rw [talks]; simp_rw [tax_one, ← map_prod]; apply PowerSeries.ext; intro n; simp only [map_sum, PowerSeries.coeff_mul_C, said,coeff_mk]; exact Eq.symm (spelled _ p)
lemma author (R:Reports G d): realm 1 R=R:=by
  ext1 n; ext1 l; ext1 t; ext1 p; have hh:= congr_arg (coeff n) (sweet R t p); simpa only [said,coeff_mk] using hh
end YM.XSpace.Normalize
