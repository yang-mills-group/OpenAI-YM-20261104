import YM.AllOrder.Fire.Rank
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Fire
open Finset Function Laplace.SigmaP Laplace PositionX.Jet PertExtension PertExtension.Series PositionX.Gauss Radial Asymptotics MeasureTheory Response
open scoped Topology ContDiff BigOperators Classical
variable {Y X:Type} [NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
local notation "Ω"=>X×Y
variable {u: ℝ→ℝ}{n j:ℕ}
lemma rank_taylor (h:Rank ℝ n u) : (∀ k,n<k→ someJ u k=0) ∧ u=delay (someJ u) n := by
 induction h with
 | nil v r=> refine ⟨fun k hk=> ((Act.static (n:=k) r).writes k le_rfl).trans (if_neg (by omega)),?_⟩; ext1 x; rw [show someJ _=just r from funext fun k=> (Act.static (n:=k) _).writes _ le_rfl]; simp [just,delay]
 | @add v f g hf hg i j=>
    rw [some_add hf.read.smooth.contDiffAt hg.read.smooth.contDiffAt]; refine ⟨fun k hk=> ?_,?_⟩; · rw [Pi.add_apply,i.1 k hk,j.1 k hk,add_zero];
    ext1 x; unfold delay; rw [Pi.add_apply,congr_fun i.2 x, congr_fun j.2 x]; simp only [delay,Pi.add_apply, smul_add, Finset.sum_add_distrib] -- orientation
 | @dot P n f h ih=>
    let v:= P 1;
    have he:(P:ℝ→ℝ)*f=v • ((fun x => x^1)*f):= by
      funext x; change P x*f x=v*(x^1*f x); have ht:P x=x*v:= by simpa [v] using! (P.map_smul x 1)
      rw [ht]; ring
    let g:= (fun x:ℝ=>x^1)*f; have hF:ContDiffAt ℝ ω f 0:= h.read.smooth.contDiffAt; have hh: ContDiffAt ℝ ω g 0:= (contDiffAt_id.pow 1).mul hF
    have hy k : someJ (v • g) k=v*(if 1≤ k then someJ f (k-1) else 0):=by rw [show someJ (v • g) k=v* someJ g k from ((eo_Act k hh).smul _).writes _ le_rfl, show g=_ from (rfl : g=(fun x:ℝ=> x^1)*f), jo_shift hF] -- unfold g
    rw [he]; refine ⟨fun k hk=> ?_,?_⟩; · change someJ (v • g) k = _; rw [hy,if_pos (by omega),ih.1 _ (by omega),mul_zero]
    ext1 x; unfold delay; change v*(x^1*f x)= ∑ i∈_,x^i* someJ (v • g) i
    rw [Finset.sum_range_succ']; simp only [hy, le_add_iff_nonneg_left, Nat.zero_le, if_true, if_neg (show ¬1≤(0:ℕ) from (by decide)), mul_zero,add_zero, Nat.add_sub_cancel]; rw [congr_fun ih.2 x]; unfold delay; simp only [smul_eq_mul,Finset.mul_sum,pow_one]; apply Finset.sum_congr rfl; intro i _; rw [pow_succ]; ring -- edit use conv
end YM.AllOrder.Fire
