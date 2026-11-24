import YM.Integration.WilsonOriginalSparseFiledPostPrice
import YM.Integration.WilsonOriginalCensusPostedWages

/-! The two native angular bills draw on the same posted cash as the original
dated census. Their extra finite numerical constant is selected before the
cutoff, period, addresses, and choice of the two presentations. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSparseFiledRosterCash
open Finset Lattice RG Wilson Marker QuadraticLocal Multi
open WilsonOriginalSparseFiledFare WilsonOriginalSparseFiledPostPrice
open scoped BigOperators Classical

def room (G:Gauge)(cap:ℕ):ℝ:=
  ∑p:Fin (cap+1),∑e:Fin (cap+1),∑r:Fin (cap+1),4*WilsonOriginalSparseFiledFare.constant G p e r

theorem all (G:Gauge)(cap p e r:ℕ)(hp:p ≤ cap)(he:e ≤ cap)(hr:r ≤ cap):
    4*WilsonOriginalSparseFiledFare.constant G p e r ≤ room G cap:=by
  let i:Fin (cap+1):=⟨p,Nat.lt_succ_of_le hp⟩
  let j:Fin (cap+1):=⟨e,Nat.lt_succ_of_le he⟩
  let k:Fin (cap+1):=⟨r,Nat.lt_succ_of_le hr⟩
  let f (a b c:Fin (cap+1)):=4*WilsonOriginalSparseFiledFare.constant G a b c
  have pos (a b c):0≤f a b c:=mul_nonneg (by norm_num) (WilsonOriginalSparseFiledPostPrice.nonnegative G a b c)
  have one:=single_le_sum (f:=f i j) (fun c _=>pos i j c) (mem_univ k)
  have two:=single_le_sum (f:=fun b=>∑c:Fin (cap+1),f i b c) (fun b _=>sum_nonneg fun c _=>pos i b c) (mem_univ j)
  have three:=single_le_sum (f:=fun a=>∑b:Fin (cap+1),∑c:Fin (cap+1),f a b c)
    (fun a _=>sum_nonneg fun b _=>sum_nonneg fun c _=>pos a b c) (mem_univ i)
  exact one.trans (two.trans three)

variable {V:Type}[DecidableEq V]{Γ:Census V} (w:Bool→V→ℝ)(s:Γ.Mode)(b:Bool→ℝ)
local notation "joint" => WilsonEmittedJoinedFares.cash s w (fun a:Bool=>if a then -1 else 1) b

theorem portion (money:∀a,0≤b a)(wallet:∀a,0<Poly.toll (w a) s)(a:Bool):
    b a/Poly.toll (w a) s ≤ joint:=by
  let term (c:Bool):=|if c then (-1:ℝ) else 1| *((Poly.toll (w c) s)⁻¹*b c)
  have whole:=single_le_sum (f:=term) (fun c _=>mul_nonneg (abs_nonneg _)
    (mul_nonneg (inv_nonneg.mpr (wallet c).le) (money c))) (mem_univ a)
  have unit:|if a then (-1:ℝ) else 1|=1:=by cases a <;> norm_num
  simpa only [WilsonEmittedJoinedFares.cash,term,unit,one_mul,div_eq_mul_inv,mul_comm] using whole

theorem funded (G:Gauge)(cap p e r d:ℕ)(a:Bool){H:ℝ}(hot:0≤H)
    (hp:p ≤ cap)(he:e ≤ cap)(hr:r ≤ cap)(fixed:room G cap ≤ H)
    (money:∀i,0≤b i)(wallet:∀i,0<Poly.toll (w i) s)
    (cash:joint ≤ 2*H^(d+1)):
    2*(WilsonOriginalSparseFiledFare.constant G p e r*b a/Poly.toll (w a) s) ≤ H^(d+2):=by
  let c:=WilsonOriginalSparseFiledFare.constant G p e r
  have positive:0≤c:=WilsonOriginalSparseFiledPostPrice.nonnegative G p e r
  have own: b a/Poly.toll (w a) s ≤ 2*H^(d+1):=(portion w s b money wallet a).trans cash
  calc
    _ = (2*c)*(b a/Poly.toll (w a) s) := by ring
    _ ≤ (2*c)*(2*H^(d+1)) := mul_le_mul_of_nonneg_left own (mul_nonneg (by norm_num) positive)
    _ = (4*c)*H^(d+1) := by ring
    _ ≤ H*H^(d+1) := mul_le_mul_of_nonneg_right ((all G cap p e r hp he hr).trans fixed) (pow_nonneg hot _)
    _ = _ := by rw [pow_succ H (d+1)];ring

end YM.Integration.WilsonOriginalSparseFiledRosterCash
end
