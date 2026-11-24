import YM.QuadraticLocal.Rebirth.Generation
/-! # Back substitution on the tier, including the error multiplier

Jobs on different Loan grades must quote actual post-step ratio discrepancy separately. Use
 `taken` along the actual trajectory in any per-site weighted norm afterwards. This file gives
 the FULL relative residual equation, including the old value at negative powers of the coupling.
 Doesn't re-choose powers at individual donor locations. Uses `g⋆` global positive for reset.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Rebirth
open Function Filter Finset Lattice RG Wilson Marker
open Comparison.RG02 Comparison.RG02.Adjacent
open Pressure ConnectedActivityE6 AllOrder AllOrder.Catch
open AllOrder.Wheel AllOrder.Floe Next.Scheduling
open PositionX.Jet AllOrder.Response PositionX.Gauss
open AllOrder.Laplace AllOrder.Laplace.SigmaP
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open Chart
namespace Balance
variable (Q : Pace.Coin) (h : Q 0=0) (L : ℕ) (s:ℤ) (t:ℝ)
local notation "u"=> tariff Q h L s
local notation "Φ" i:max=> Pace.ladder (grade (s+((i:ℕ):ℤ))) Q
noncomputable def profile (n:ℕ) := ∑ i∈range (n+1), (u) i*t^i*delay ( Φ i ) (n-i) t

private lemma walk_next (n i:ℕ) (hm:i≤n): t^i*delay ( Φ i ) (n+1-i) t=t^i * delay ( Φ i ) (n-i) t+t^(n+1)*( Φ i ) (n+1-i) := by unfold delay; have hu:n+1-i=n-i+1:= (by omega); rw [hu, Finset.sum_range_succ (n:=n-i+1), mul_add, smul_eq_mul, ← mul_assoc (t^i), ← pow_add, show i+(n-i+1)=n+1 from (by omega)];
-- Real reparameterization is simply THIS identity with Taylor errors on individual steps.
lemma even (n:ℕ) (hn:n≤ L): profile Q h L s t n=1 := by
    induction n with
    | zero=> simp [profile, tariff_zero, delay, Pace.start _ h]
    | succ k ih=>
       rw [← ih (by omega)]; unfold profile; rw [ Finset.sum_range_succ (n:=k+1) ]; let m:=k+1; let K i := (u) i * ( Φ i ) (m-i); have hp: (∑ i∈range m,K i)+K m=0:= Eq.trans ((Finset.sum_range_succ (n:=m) K).symm) (charges Q h L s m m hn le_rfl);
       let f i:= (u) i*t^i*delay ( Φ i ) (k-i) t;
       have hs:(u) m*t^m* delay ( Φ m ) (m-m) t=t^m * K m:= by unfold delay K; simp [Pace.start _ h]; ring
       rw [sum_congr rfl (g:=fun i=> f i+t^m*K i) (fun i hi=>?_ ), sum_add_distrib, ← Finset.mul_sum,hs,add_assoc, ←mul_add,hp,mul_zero,add_zero] -- rw under sums
       have hx : i≤ k:= mem_range_succ_iff.mp hi; unfold f K; rw [mul_assoc ((u) i), walk_next Q s t k i hx]; change (u) i*(t^i*(_ : ℝ)+t^m*( Φ i ) (m-i))=_; ring
-- program use at actual next post. Sign choice for `OldErr` adds actual−model.
variable (k:ℝ)
noncomputable def taken (n:ℕ):ℝ:=∑ i∈range (n+1), (tariff Q h L s i)*t^i*(k/t) ^ (s+(i:ℤ)) -- sign positive
noncomputable def balance (n:ℕ):ℝ:=1-Balance.taken Q h L s t k n
lemma renewed (n:ℕ)(ht:t≠0)(hk:k≠0): t^s= (∑ i∈range (n+1),(tariff Q h L s i)* k^(s+(i:ℤ)))+balance Q h L s t k n * t^s := by
    unfold balance taken; rw [sub_mul, one_mul, Finset.sum_mul]; nth_rw 1 [Finset.sum_congr rfl (g:=fun i=> ( (tariff Q h L s i)* t^i*(k/t) ^ (s+(i:ℤ)) ) * t^s) (fun i _=>?_)];
    · abel
    rw [div_zpow, zpow_add₀ ht,zpow_natCast]; set a:=k ^ (s+(i:ℤ)); field_simp
lemma remainder (n:ℕ)(he:n≤L): balance Q h L s t k n= -(∑ i∈range (n+1), (u) i*t^i*((k/t) ^(s+(i:ℤ)) -delay ( Φ i ) (n-i) t)) := by
    unfold balance; rw [← even Q h L s t n he]; simp_rw [mul_sub,sum_sub_distrib,neg_sub]; rfl -- test
end Balance
end YM.QuadraticLocal.Rebirth
