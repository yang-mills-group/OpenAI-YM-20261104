import YM.Qlocal.Quipu.Lagger
import YM.Qlocal.Quipu.Turbin
import YM.Qlocal.Sequence
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Marker Comparison.RG02.Order Comparison.RG02.Assembly
open AllOrder Fire Response PertExtension PertExtension.Series Radial PositionX.Jet PositionX.Gauss
open scoped Topology ENNReal ContDiff BigOperators Classical
open Finset
namespace Wall
variable {V:Type}[DecidableEq V][Fintype V]{R:Census V} {Z X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
  {σ:Type}[Fintype σ] {k n r :ℕ} (M:(σ→ℝ)→L[ℝ]X) (x:X) (Y:σ→Poly R)
variable {p : Book X} (h:Clear p) (hp:p 0=0) (P Q:X→ℝ)
open Turbin
local notation "s"=> (σ→ℝ)
def polar (P:X→ℝ) (Z:σ→ℝ):=P (x+M Z)
local notation "ν"=> polar M x
abbrev orientation (p:Book X):= PowerSeries.mk fun j=> wall Y (polar M x (p j))
local notation "S"=> orientation M x Y
lemma pre_s (b:ℝ)(P:X→ℝ): (b • ν P)=ν (b•P):=rfl
lemma pre_a (P Q:X→ℝ): ν P+ν Q=ν (P+Q):= rfl
lemma pre_m (P Q:X→ℝ): ν P*ν Q=ν (P*Q):= rfl
lemma finite_path {J:Type*}(T:Finset J)(F:J→X→ℝ): ν (∑ i∈T,F i)=∑ i∈T,ν (F i):= by ext1 b; unfold polar; simp only [Finset.sum_apply]
lemma granted (h:Plausible P): Plausible (polar M x P):=nearStep (B:=M.toLinearMap) x h
include h
lemma spotted (k n:ℕ) : wall Y (polar M x (energy p k n))= PowerSeries.coeff n ((S p)^k):= by
 let y:= S p; induction k generalizing n with
 | zero=> rw [level,pow_zero,PowerSeries.coeff_one]; by_cases he:n=0;
          · subst n; change wall Y (fun _=>1)=_; rw [sky_c,map_one,if_pos rfl]
          rw [if_neg he, show ν (wirings (X:=X) (fun _=>1) n)=(fun _=>0) from funext fun i=> if_neg he]; exact (sky_c _ 0).trans (map_zero _)
 | succ k ih=>
    have ht(k n:ℕ):Plausible (energy p k n):= square_p (u:=p) h k n
    let U:= σ→ℝ
    have he: energy p (k+1) n=∑ i∈antidiagonal n, energy p k i.1 * p i.2:= by
       ext1 i; change PowerSeries.coeff n ((PowerSeries.mk fun j=> p j i)^(k+1))= _; rw [pow_succ,PowerSeries.coeff_mul]; simp only [PowerSeries.coeff_mk,Finset.sum_apply]; rfl -- unfolds swap & energy occurrences.R inspect
    rw [he,finite_path, Turbin.pours, pow_succ,PowerSeries.coeff_mul]; refine Finset.sum_congr rfl (fun i _=>?_); swap
    · intro i _; exact granted M x _ ((ht k _).mul (h _))
    rw [← pre_m, pours_m _ (granted M x _ (ht k _)) (granted M x _ (h _)), ih, PowerSeries.coeff_mk]
include hp
open Comparison.RG02.Order.Join
lemma recorded (k:ℕ): series R k (S (EXP p)) = Poly.pass (series R k (S p)):= by
 let P:= S p; let n:=Fintype.card (V ⊕ Fin k); let E:=∑ i∈range (n+1),(i.factorial:ℂ)⁻¹ • P^i
 have hh : series R k (S (EXP p))=series R k E:= by
    apply both_parts; intro i v; have ht:= order_limit k v; let j:= v.val.card; have hj: j ≤ n:=ht.trans (by simp [n]);
    have hx(j'):j' ≤ n → PowerSeries.coeff j' (S (EXP p))=PowerSeries.coeff j' E:= by
       intro hj; let f (i:ℕ):=(i.factorial:ℝ)⁻¹ •(energy p i j'); let T:= ∑ i∈range (n+1), f i
       rw [PowerSeries.coeff_mk, show EXP p j'=T from ((Expo hp hj).trans ?_)]; swap; · rw [Response.arrow, Finset.sum_apply]; simp only [f,T, Pi.smul_apply] -- inspect
       unfold T E; rw [finite_path, Turbin.pours _ _ _ (fun i _=> granted M x _ ((square_p (u:=p) h i j').scale _)),map_sum]; apply Finset.sum_congr rfl; intro i _; rw [PowerSeries.coeff_smul];  rw [← pre_s, pours_s _ (granted M x _ (square_p (u:=p) h i j')), spotted M x Y h];
       rw [← Complex.ofReal_natCast,← Complex.ofReal_inv]; rfl
    rw [polarization,polarization, hx j hj] -- `j` reducible?
 unfold Poly.pass; rw [hh]; unfold E; rw [map_sum]; simp_rw [series_smul,map_pow]; rfl
lemma zero_born : (series R r (S p)).part (Board R r).quiet=0:= by
 rw [← pair_quiet,polarization]; change (Nat.factorial _ :ℂ) * ((PowerSeries.coeff 0 (S p)).part _)=0; rw [PowerSeries.coeff_mk, hp]; change _*(wall Y (fun _=>0)).part _=_; rw [sky_c, map_zero,Poly.part_nil, mul_zero]
omit hp
variable {q:Book X} (hh:Clear q)
include hh
lemma cost_sub : series R r (S (p-q))= series R r (S p) - series R r (S q):= by
 rw [← map_sub]; apply congr_arg; ext1 i; rw [map_sub, PowerSeries.coeff_mk,PowerSeries.coeff_mk,PowerSeries.coeff_mk]
 let y:= orientation M x Y; simp_rw [sub_eq_add_neg, show -q=(-1:ℝ) • q from (neg_one_smul ℝ _).symm]; change wall Y (ν (p i+(-1:ℝ) • q i))= _; rw [← pre_a,pours_a _ (granted M x _ (h _)) (granted M x _ ((hh i).scale _)),← pre_s, pours_s _ (granted M x _ (hh i)),neg_one_smul]
end Wall
end YM.Qlocal.Quipu
