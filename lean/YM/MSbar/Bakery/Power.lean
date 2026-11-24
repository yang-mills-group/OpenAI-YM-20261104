import YM.MSbar.Bakery.Value
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bakery
open Function Filter Finset Cacao MeasureTheory Whisk
open scoped Topology BigOperators Classical ContDiff
variable {σ ι :Type}[Fintype σ] [DecidableEq σ]
open Lattice MvPolynomial Analysis Set Metric
local notation "P"=>Pot σ
local notation "V"=>View σ
variable {x y:View σ}{f g: View σ→ℝ}{F:Pot σ}{X:Set (View σ)}{p m k q :ℕ}{u t a r b:ℝ} {n:Side}{l:σ→ Site n}{Y W:Finset (Site n)}
lemma valor_eq (T:List σ): value l W a p x (fun i=>eval i F) T= rate l W a p x F T:=by unfold value rate; rw [glance_jet]
lemma crests (hv: Phase l W a p k (fun i=>eval i F) X b)(h:x∈X) : lump l W a p k x F≤ b:=by
   refine le_trans (le_of_eq ?_) (hv.2 (fun _=> x) (fun i=> h))
   exact stitch _ fun i hi=>(valor_eq i).symm
-- transport along fields.Output port.Power.Word.St.Word.W.
lemma spice_fund (ha:0≤ a) (hf: F.totalDegree≤m)(ht:Vault l W a p m x F t)(hp:0≤b) (k:ℕ) : Phase l W a p k (fun i=>eval i F) (closedBall x b) ( t * (1+b)^(m+1)):= by
   let e:=closedBall x b; let g(i:View σ):= eval i F; have he:e.Nonempty:=⟨x,mem_closedBall_self hp⟩; have hy:=ht.1
   let H(k :ℕ)(cP:ℝ):=Phase l W a p k g e cP
   have hi (k:ℕ)(he:m< k)(α:ℝ)(hzp: 0≤ α): H k α := ⟨hzp,fun f h=>?_⟩
   · by_cases hx:k≤ m+1; swap;· exact hi k (by omega) _ (by positivity)
     have hz(k:ℕ) : k≤ m+1 → H k (t*(1+b)^(m+1-k)):=by
         intro he; induction he using Nat.decreasingInduction with
         | self=> exact hi _ (by omega) _ (by positivity)
         | of_succ k hk ih=>
              have hB:k≤m:=by omega
              let a' := t*(1+b)^(m+1-(k+1)); refine ⟨by positivity,fun f' hv=>?_⟩
              have hx :Yarn k (fun L=> value l W a p (f' L) g L)≤ Yarn k (fun L=>spread l W a p L * |glance g L (f' L)-glance g L x|)+lump l W a p k x F :=by
                 unfold lump; rw [← pockets]; apply shiny; intro i hi; rw [← valor_eq]; unfold value
                 have hv : |glance g i (f' i)| ≤ |glance g i (f' i)-glance g i x|+ |glance g i x|:=by nth_rw 1 [show glance g i (f' i)=glance g i (f' i)-glance g i x+glance g i x by abel]; exact abs_add_le ..
                 rw [←mul_add]; exact mul_le_mul_of_nonneg_left hv ((effect ..).le)
              have hz:∀ i,‖f' i-x‖ ≤ b:=fun i=>by simpa [e,dist_eq_norm] using hv i
              refine hx.trans ((add_le_add (costMove (m:=m) ha (convex_closedBall ..) hB (fun i _=>(vent F|>.contDiffAt.of_le le_top)) _ _ hv (fun _=>mem_closedBall_self hp) hz ih) (ht.2 _ hB)).trans ?_)
              have he: t≤a':= le_mul_of_one_le_right hy (one_le_pow₀ (le_add_of_nonneg_right hp)); rw [show m+1-k=m+1-(k+1)+1 by omega, pow_succ]; change b*a'+t≤ _; unfold a' at *; linarith only [he]
     obtain ⟨ha,hv⟩:=hz k hx; refine ⟨ha.trans ?_,fun a b=> (hv a b).trans ?_⟩ <;> apply mul_le_mul_of_nonneg_left ?_ hy <;> exact pow_le_pow_right₀ (le_add_of_nonneg_right hp) (Nat.sub_le ..)
   apply le_trans (le_of_eq _) hzp; refine (stitch (f:=fun L=>value l W a p (f L) g L) (g:=fun _=> (0:ℝ)) k ?_).trans (spool k); intro i h; unfold value g; rw [glance_jet,blank_list,abs_zero,mul_zero]; exact hf.trans_lt (he.trans_eq h.symm)

lemma smoothP (F:Pot σ)(B t: View σ) : HasDerivAt (fun r:ℝ=> eval (B+r • t) F) (∑ i, t i * eval B (pderiv i F)) 0 :=by
   have hp:= (lamp (f:=fun v=>eval v F) B t 0 ((vent F).contDiffAt.differentiableAt (by simp))); simp_rw [TonD] at hp; simpa using hp
end YM.MSbar.Bakery
