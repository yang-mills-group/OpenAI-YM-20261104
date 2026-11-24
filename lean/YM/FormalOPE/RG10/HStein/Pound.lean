import YM.FormalOPE.RG10.HStein.Ready
/-!
 # Sum transfers and replot types, including exponentials
 Powers of cost rather than finite-dimensional but volume dependent constants. May use
 arbitrary Lens and either rescale direction. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.HStein
open Route Route.Bulk PowerSeries
open MvPolynomial (totalDegree)
open Finset Function
open Multi.Vacuum.Gauss Tier
open scoped Topology BigOperators Classical
variable {I B J Y:Type} [Fintype J]
variable {T:Tape Y} {p:I⊕B → Y} (O:Lens T){q:I→Row J}{V:Channel (I⊕B)}
local notation "Z"=> Index I B
local notation "A"=> O.m ∘ p
local notation "Γ"=> O.m ∘ (p ∘ Sum.inr)
variable {F:Tier} {r k j i d n:ℕ} {C:ℝ}
variable (X: Packet (I⊕B))

namespace Tier
-- note `F` implicit outer
variable (F) (w v:I→ℝ) (hw:0≤w) (T U:Channel I)

lemma all_gain : F.gain w T k=∑ i∈range (k+1),F.valueOf w (coeff i T):= rfl
lemma coin_steady (c: ℂ) : F.gain w (c•T) k= ‖c‖ * F.gain w T k:= mag_smul ..
lemma once : F.gain w 1 k=1:= mag_one ..
lemma near_eq (h:Through k T U):F.gain w T k=F.gain w U k:= mag_ext _ _ _ _ _ h
include hw
lemma collect : 0≤ F.gain w T k:= mag_sign _ _ _ (F.dep_sign w hw) _
lemma sumUp {B :Type*} (T : Finset B) (x : B→ Channel I): F.gain w (∑ i∈T,x i) k≤ ∑ i∈T,F.gain w (x i) k:= mag_sum _ _ _ (F.dep_sign w hw) _ _
lemma now (hi:i≤k): F.valueOf w (coeff i T)≤ F.gain w T k:= current _ _ _ (F.dep_sign w hw) _ _ hi
lemma gain_mul : F.gain w (T*U) k ≤ F.gain w T k * F.gain w U k:= mag_mul _ _ _ (F.dep_sign w hw) _ _
lemma gain_moment {G:Tier} (h:∀ a≥0,F.value a ≤ G.value a) : F.gain w T k ≤ G.gain w T k:= w_le _ _ _ _ (F.dep_sign w hw) _ (fun i=> sub_le_sub_right (h (w i) (hw i)) _)
lemma gain_classical : (pol n).gain w T k=mag w n k T:= by rw [all_gain,mag]; exact sum_congr rfl (fun i _=> ordinary w (coeff i T) n hw) -- maybe order
lemma gain_under (h : w ≤ v): F.gain w T k ≤ F.gain v T k:= w_le _ _ _ _ (F.dep_sign w hw) _ (fun i=> sub_le_sub_right (F.near (hw i) (h i)) _)
lemma gain_alternate {d:ℝ} (hd:0≤d) (hv: 0 ≤ v)(hx:∀ a,w a ≤ d+v a): F.gain w T k ≤ F.value d * F.gain v T k:= by
 simp_rw [all_gain, mul_sum]; apply sum_le_sum; intro i _
 rw [F.capital w hw, F.capital v hv, mul_sum]; apply sum_le_sum; intro a ha
 have he : along w a.support ≤ d+along v a.support:= along_le w a.support (add_nonneg hd (along_nn hv a.support)) (fun b hb=>(hx b).trans (by gcongr; exact le_along hb v))
 rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right ((F.near (along_nn hw _) he).trans (F.toll hd (along_nn hv _))) (norm_nonneg _)

private def coup (G:Tier) := ∑ i∈ range (k+1), ∑ j∈ antidiagonal i, F.valueOf w (coeff j.1 T) * G.valueOf w (coeff j.2 U)
-- implicit k in def must included result? def not using index binder... ok see
private lemma matrix (G:Tier): F.coup (k:=k) w T U G ≤ F.gain w T k * G.gain w U k:= by
 unfold coup; apply (triangle_le _ _ ?_).trans; apply Eq.le; simp_rw [all_gain,sum_mul_sum];
 exact fun i=> mul_nonneg (F.lower _ hw _) (G.lower _ hw _)
lemma twice_all : F.gain w (T*U) k ≤ free.gain w T k * F.gain w U k + F.gain w T k*free.gain w U k:= by
 apply le_trans _ (add_le_add (free.matrix w hw T U F) (F.matrix w hw T U free)); unfold coup; rw [all_gain, ←sum_add_distrib]; apply sum_le_sum; intro i _
 rw [coeff_mul,←sum_add_distrib]; exact (many F _ hw _ _).trans (sum_le_sum (fun _ _=> twice F w hw _ _)) -- include hw explicit?
omit hw in
lemma gain_constant (T:Packet I) : F.gain w (PowerSeries.C T) k=F.valueOf w T:= by unfold gain; unfold mag; rw [sum_range_succ']; simp [valueOf] -- C collision binder. inspect
end Tier

variable (U: readyNow q V O p d r C F) (hV : Guard V r 0) (hV' : coeff 0 V=0)
variable [Fintype I] [DecidableEq I]
variable (B₀:Rails q V r p T F C) (hc : 2≤C) (hr:(r+1:ℝ)≤C) (hd:(d+3*r:ℝ) ≤ C) (hk:k ≤ r)
local notation "Bf"=> C^(6*d)
local notation "B₀f"=> C^(6*(d+3*r))

include U hk in
omit [Fintype I] [DecidableEq I] in
lemma pays (H : totalDegree X + 3*k ≤ d): F.valueOf Γ (opt q V k X) ≤ Bf * F.valueOf A X:= by
 nth_rw 1 [resolves X]; rw [map_sum]; apply (F.many Γ (nout O p) _ _).trans
 rw [F.capital _ (nnews O p), mul_sum]; apply sum_le_sum;intro i hi;
 rw [_root_.map_smul, F.coins];
 have hs := (show Primitives.GCC.LocalPolynomial.length i ≤totalDegree X from MvPolynomial.le_totalDegree hi)
 exact (mul_le_mul_of_nonneg_left (U k hk i (by omega)) (norm_nonneg _)).trans (le_of_eq (by ring)) -- inspect

local notation "W"=> Channel (I⊕B)
include B₀ hV hV' hc hr hd in
lemma easy (M:W)(hm:Guard M r d): F.gain Γ (transfer q M V) r ≤ C*B₀f * F.gain A M r := by
 have H : 0 ≤ C := le_trans (by norm_num) hc
 have hb:= F.collect A (nnews O p) M (k:=r)
 have he: readyNow q V O p (d+3*r) r C F := priced O hV hV' B₀ hc (by linarith) (by push_cast; exact hd) -- cast positivity linarith?
 let h : ℕ×ℕ→ℝ:= fun i=> B₀f*F.valueOf A (coeff i.1 M)
 rw [all_gain]; apply le_trans (b:=∑ i∈range (r+1), ∑ j∈antidiagonal i, h j) (sum_le_sum fun i hi=> ?_) ((triangle_le r h ?_).trans ?_)
 · exact fun i=> mul_nonneg (pow_nonneg H _) (F.lower A (nnews O p) _)
 · unfold h; simp only [sum_const, nsmul_eq_mul,card_range]; rw [←Finset.mul_sum,←mul_sum,F.all_gain]; push_cast; rw [mul_assoc]; gcongr
 have hk : i≤r:= Nat.le_of_lt_succ (mem_range.mp hi)
 rw [rational]; apply (many F Γ (nout O p) _ _).trans; refine sum_le_sum fun j hj=> pays O (coeff j.1 M) he (by have ht:= mem_antidiagonal.mp hj; omega) ?_
 have ht := mem_antidiagonal.mp hj; have H := hm _ (show j.1 ≤ r by omega); omega
end YM.FormalOPE.RG10.HStein
