import YM.AlbaMS.Cutis.Front

/-!
# geometry Gram and gauge section for trustees

Do all on scalar kernels first, projectors include the factor half where used
as projections (not prematurely installing them in inversion image C!). Need
θ_ghost even including fixed points. Here `n` must be even for some link equations;
means full-site counting, not rep-count. Use physical-root link `clock`. Count
link units in both traces once per orbit in based.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis.Winter
open Set Function Filter LinearMap Matrix
 open scoped BigOperators Classical Topology Matrix
open Bric Loft Inlay Inlay.Net Odom Lattice Nexus
variable {n : Side}{E:Type*}{G:Gauge}(n)(b:Bool)
abbrev baseCell (i:Nail n true): Vtx n:= i.val.val
abbrev toneAddr (v:Vtx n):= (silver n).pick v
def thorn : Matrix (Arm n) (Foil n) ℝ:= of fun i j=> if (copper n).pick i=j then sting (typeFlip n i) (1:ℝ) else 0
def shrub : Matrix (Vtx n) (Nail n b) ℝ:= of fun i j=> if slur b i=some j then 1 else 0
-- shape and count
lemma paidT : Φ (walkT n G b)= dotC G (thorn n):=by
  ext ⟨i,u⟩ ⟨j,v⟩; simp only [Φ,of_apply]; rw [(walkT n G b).phi_rule]; have he : W_adj (G:=G) 1 u v= if u=v then 1 else 0:= by rw [W_adj,printC,toMatrix_apply,Gauge.adjoint_one]; change coefQ u (base G v)=_; rw [coef_base]; simp [eq_comm]
  simp only [walkT,dotC,chip,thorn,Matrix.of_apply,he]; split_ifs <;> simp_all
lemma paidS : Ψ (walkT n G b)= dotC G (shrub n b):=by
  ext ⟨i,u⟩ ⟨j,v⟩; simp only [Ψ,of_apply]; rw [(walkT n G b).eps_rule]; have he: W_adj (G:=G) 1 u v= if u=v then 1 else 0:= by rw [W_adj,printC,toMatrix_apply,Gauge.adjoint_one]; change coefQ u (base G v)=_; rw [coef_base]; simp [eq_comm]
  simp only [walkT,dotC,chip,shrub,Matrix.of_apply,he]; split_ifs <;> simp_all
variable {n:Side}
variable (h: Even n.val)
include h
lemma stalkInvert (x:Arm n) : typeFlip n ((copper n).σ x)= !(typeFlip n x):=by
  unfold typeFlip; rcases (copper n).split x with H|H<;> rw [Token.share, show (copper n).chief x=_ from H] <;> simp [cop_nofix h x, Ne.symm (cop_nofix h x)] -- h included?
lemma centerEq : aura n * thorn n=thorn n:=by
  ext x y; rw [aura_left]; simp_rw [thorn,Matrix.of_apply,Token.pick_σ, stalkInvert h]; split<;> first| exact neg_zero| (cases typeFlip n x<;>simp)
lemma stalkRound : thorn n*(thorn n)ᵀ=1+aura n:=by
  ext i j; rw [Matrix.mul_apply,Finset.sum_eq_single ((copper n).pick i)];
  · rcases (copper n).pick_eq i j with ⟨he,hp⟩; rw [Matrix.add_apply, Matrix.one_apply];
    by_cases hx:i=j
    · subst j; simp only [aura,veil,thorn,Matrix.of_apply, Matrix.transpose_apply, if_true,Matrix.neg_apply]; rw [if_neg (cop_nofix h i)]; cases typeFlip n i <;> simp
    by_cases hu:(copper n).σ i=j
    · have heq:= hp (Or.inr ((copper n).invol i|>.symm.trans (congr_arg (copper n).σ hu)))
      unfold aura veil thorn; simp only [Matrix.of_apply, Matrix.transpose_apply, Matrix.neg_apply,if_pos heq.symm, if_pos hu, if_neg hx]; rw [← hu, stalkInvert h]; cases typeFlip n i<;> simp
    unfold aura veil thorn; have hh:(copper n).pick j≠ (copper n).pick i:=mt ((copper n).pick_eq j i).1 (by push Not; exact ⟨Ne.symm hx,Ne.symm hu⟩); simp [Matrix.transpose_apply,hx,hu,hh]
  intro x _ hx; simp [thorn,Ne.symm hx]; simp
lemma stalkSeal : (thorn n)ᵀ*thorn n=(2:ℝ) • 1:=by
  ext i j; rw [Matrix.mul_apply]; by_cases he:i=j
  · subst j
    have ht (x:Arm n): (thorn n)ᵀ i x*thorn n x i=if (copper n).pick x=i then 1 else 0:=by simp only [Matrix.transpose_apply,thorn,Matrix.of_apply]; cases typeFlip n x <;> split_ifs <;> simp
    simp_rw [ht]; rw [(copper n).sum_groups (fun j=> if j=i then (1:ℝ) else 0), Finset.sum_eq_single i]; simp [Token.extra,cop_nofix h i.val]; intro x _ hx; simp [hx];simp
  rw [Finset.sum_eq_zero]; simp [he]; intro x _; by_cases hx:(copper n).pick x=i; simp [thorn,hx,he]; simp [thorn,hx]
-- shrub ghost
omit h in
lemma hedge : flow n * shrub n b=shrub n b:=by ext x y; rw [flow_left]; simp only [shrub, Matrix.of_apply,slur_neg]

omit h
def peg (n:Side) : Matrix (Nail n true) (Vtx n) ℝ:= Matrix.of fun x y=>
    (1/2)*((if baseCell n x=y then 1 else 0)+(if -baseCell n x=y then 1 else 0))-(if y=0 then 1 else 0)
lemma peg_left (P:Matrix (Vtx n) E ℝ)(x y): (peg n * P) x y=
    (1/2)*(P (baseCell n x) y+P (-(baseCell n x)) y)-P 0 y:=by simp [Matrix.mul_apply, peg, add_mul, ite_mul, sub_mul, Matrix.of_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, mul_add] -- fix
lemma peg_mean : peg n*mean n=0:=by ext i j; rw [peg_left]; change _*(fee n+fee n)-fee n=0; ring
lemma atzero : slur (n:=n) true (0:Vtx n)=none:=by
  cases h:slur (n:=n) true 0 with|none=>rfl|some v=> have he:= notches (n:=n) true 0; simp [h] at he
lemma petal : peg n * shrub n true=1:=by
  ext i j; have h (x:Site n): shrub n true x j=if slur true x=some j then 1 else 0:=rfl
  rw [peg_left,h,h,h,atzero,if_neg (show (none:Option (Nail n true)) ≠ some j by simp),slur_neg,show slur true (baseCell n i)=some i from slur_hp .., Matrix.one_apply]; by_cases ht:i=j<;> norm_num [ht]
lemma peg_feed : peg n*flow n=peg n:= by ext i j; rw [flow_right]; simp [peg,neg_eq_iff_eq_neg,add_comm,neg_neg]
def basisRow (n:Side) : Cell n:= of fun _ j=>if j=0 then 1 else 0
lemma mean_basis : mean n*basisRow n=basisRow n:=by
  ext i j; simp only [basisRow,mean,Matrix.mul_apply,Matrix.of_apply]; split; simp only [mul_one, Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; rw [mul_comm]; exact fee_o _; simp
lemma meet : shrub n true*peg n=(1/2:ℝ) • (1+flow n)-basisRow n:=by
  ext i j; rw [Matrix.mul_apply]; cases hi:slur true i with
  | none=> have he : i=(0:Site n):= by by_contra h; have hu: (slur true i).isSome:= (notches ..).2 (Or.inr h); simp [hi] at hu
           subst i; unfold flow basisRow; simp [shrub,hi,veil,silver, Matrix.one_apply,eq_comm]; split_ifs <;> norm_num
  | some w=>
    rw [Finset.sum_eq_single w];
    · have hv:(silver n).pick i=w.val:=by unfold slur recede at hi; split at hi <;> first| exact congr_arg Subtype.val (Option.some.inj hi)| simp at hi
      simp only [shrub,Matrix.of_apply,hi,if_true,one_mul, flow, basisRow, Matrix.sub_apply,Matrix.add_apply,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul,veil,peg];
      rcases (Token.pick_eq (silver n) i (baseCell n w)).1 (hv.trans (Token.picked ..).symm) with h|h
      · rw [h]; by_cases hv:- baseCell n w=j <;> by_cases ht:baseCell n w=j<;> simp only [ht,hv, silver,↓reduceIte]
      rw [h, (silver n).invol]; by_cases hv:-baseCell n w=j <;> by_cases ht:baseCell n w=j<;> simp [ht,hv, silver, add_comm]
    · intro x _ hx; simp [shrub, hi,Ne.symm hx]
    simp
end YM.MSBar.Cutis.Winter
