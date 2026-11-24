import YM.MSbar.CrossH.Mug
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.CrossH
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice
open scoped Topology BigOperators ContDiff Classical
variable {σ ι:Type}[Fintype σ][DecidableEq σ]
open Polynomial MvPolynomial
local notation "P"=> Cacao.Pot σ
local notation "X"=> Positions σ
variable {n:Side}{l:σ→Site n}{a b w t u:ℝ}{p:Pot σ}{m s k:ℕ}(z:σ→σ→ℝ)
structure Tin (l:σ→Site n)(a:ℝ)(s m:ℕ)(w:ℝ)(p:Pot σ)(t:ℝ): Prop where
    dec : 0≤t
    fan : ∀ j≤ m,∀ i:σ,cog l a s p j i ≤ t/w^(j+1)
local notation "K!"=>Tin l a s m w
namespace Tin
variable {f g:Pot σ}(hw:0<w)
include hw
lemma it (h:Tin l a s m w f t)(hv:t≤u)(hk:k≤ m) : Tin l a s k w f u:=by
    refine ⟨h.1.trans hv,fun j hj i=> (h.fan _ (hj.trans hk) _).trans (div_le_div_of_nonneg_right hv ?_)⟩; exact pow_nonneg hw.le _ -- include hw
lemma aspires (h:Tin l a s m w f t)(hf:f.totalDegree≤ m+1)(k:ℕ) : Tin l a s k w f t:=by
    refine ⟨h.1,fun j hj i=>?_⟩; by_cases he:j≤ m; exact h.fan _ he _
    rw [whole f hf j (by omega)]; exact div_nonneg h.1 (pow_nonneg hw.le _)
lemma unite (h:Tin l a s m w f t)(hg:Tin l a s m w g u): Tin l a s m w (f+g) (t+u):=⟨ add_nonneg h.1 hg.1,fun i hi p=> by rw [add_div]; unfold cog; rw [_root_.map_add]; exact (lump.addition ..).trans (add_le_add (h.fan i hi p) (hg.fan i hi p))⟩
lemma pool (F:ι→Pot σ)(A: Finset ι)(t:ι→ℝ)(h:∀ i∈A,Tin l a s m w (F i) (t i)):Tin l a s m w (∑ i∈A,F i) (∑ i∈A,t i):=by
    refine ⟨Finset.sum_nonneg fun i hi=> (h i hi).1,fun j hj p=>?_⟩; rw [Finset.sum_div]; unfold cog; rw [_root_.map_sum]; exact (lump.totals ..).trans (Finset.sum_le_sum fun i hi=> (h i hi).fan j hj p)
lemma real (r:ℝ)(h:Tin l a s m w f t): Tin l a s m w (r • f) (|r| *t):= by refine ⟨mul_nonneg (abs_nonneg _) h.1,fun j hj i=>?_⟩; rw [mul_div_assoc, cog, Derivation.map_smul,lump.smul]; exact mul_le_mul_of_nonneg_left (h.fan j hj i) (abs_nonneg _)
lemma weightTok (h:1≤w)(ht:Tin l a s m w p t): Tokew l a s m 0 p t:= by
    refine (token p).mpr ⟨ht.dec,fun j hj i=>?_⟩; exact (ht.fan _ hj i).trans (div_le_self ht.dec (one_le_pow₀ h))
lemma lit (h:1≤w)(ht:Tokew l a s m 0 p t): Tin l a s m w p (w^(m+1)*t):=by
    have hx:0≤ t:= ht.1; have hv:0 < w:= zero_lt_one.trans_le h
    refine ⟨by positivity,fun j hj i=>?_⟩; refine ((token p).mp ht|>.2 _ hj i).trans ?_; rw [le_div_iff₀ (by positivity),mul_comm]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h (Nat.add_le_add_right hj _)) hx
lemma constant (r:ℝ)(he:0 ≤ t): Tin l a s m w (MvPolynomial.C r) t:= by
    refine ⟨he,fun j hj i=>?_⟩; simp only [cog,pderiv_C,lump.zeroL, div_nonneg he (pow_nonneg hw.le _)]
variable (ha:0≤a)(hv:LoopNet l a s z b)
include ha hv
lemma heat (F:Pot σ)(W:Finset (Site n))(hk: lump l W a s (m+2) 0 F≤t): lump l W a s m 0 (stove z F) ≤ b*t:= by
    let L:(Finset (Site n)) → P → ℝ:=fun W F=> lump l W a s m 0 F
    rw [stokes]; refine (lump.totals ..).trans ?_; have he:=hv.hope
    let I(i:σ)(j:σ) := pderiv i (pderiv j F)
    have hh : (∑ j:σ,∑ i:σ,L (insert (l i) (insert (l j) W)) (I i j)) ≤ t:=by
        rw [down] at hk; simp_rw [down _ _ _ _ s a m] at hk; exact hk
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hh he); rw [Finset.sum_comm (f:=fun j i=> L _ (I i j)),Finset.mul_sum]; refine Finset.sum_le_sum fun i _=>?_ ; rw [Finset.mul_sum]; refine (lump.totals ..).trans (Finset.sum_le_sum fun j _=>?_ ); rw [lump.smul,abs_div,abs_of_pos (by norm_num : 0 < (2:ℝ))]
    apply mul_le_mul ((div_le_self (abs_nonneg _) one_le_two).trans (hv.single ha i j)) ?_ (lump.nonneg ..) he; apply shiny; intro j he; unfold rate; refine mul_le_mul_of_nonneg_right (w_more (intr ?_) ha s) (abs_nonneg _); unfold zone; gcongr;grind
lemma weather (h:Tin l a s (m+2) w p t): Tin l a s m w (stove z p) (b*t/w^2):=by
    refine ⟨div_nonneg (mul_nonneg hv.hope h.dec) (sq_nonneg _),fun i hi j=>?_⟩; unfold cog; rw [← lever]
    apply (heat z hw ha hv _ _ (m:=i) (h.fan (i+2) (Nat.add_le_add_right hi 2) j)).trans; exact le_of_eq (by ring) -- needs divisions? CommRing inverse powers.Mathlib
end Tin
end YM.MSbar.CrossH
