import YM.MSbar.Tonic.Modest
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bout
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Set
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {σ ι: Type}[Fintype σ][DecidableEq σ]{f:View σ→ℝ}{D B r:ℝ}{m p q:ℕ}
local notation "W"=>blockTaylor p f
local notation "A!"=> iteratedFDeriv ℝ
lemma depart (v:View σ)(h:m>p) : iteratedFDeriv ℝ m (blockTaylor p f) v=0:=by
    let u:=∑ j∈Finset.range (p+1), potter f j; have hk:u.totalDegree≤p:= totalDegree_finsetSum_le fun v hv=>(potsD f _).trans (Nat.lt_succ_iff.mp (mem_range.mp hv)); have hz: blockTaylor p f=clue u:=by funext x; unfold blockTaylor u clue; rw [Finset.sum_apply,_root_.map_sum]; exact Finset.sum_congr rfl (fun _ _=> (pots ..).symm)
    -- basis uniqueness via derivative.eval multilinear.
    let H:= iteratedFDeriv ℝ m (blockTaylor p f) v
    have he(k:Fin m→σ) : H (fun i=>Uniform.bolt (k i))=0:=by
       let l:=List.ofFn k
       have ht : l.length=m:=by unfold l; simp
       have hp: buoy W v l=0:=by rw [hz,tours]; exact Bakery.blank_list u l (hk.trans_lt (h.trans_eq ht.symm))
       have hx:(l.map (@bolt σ)).length=m:=by rw [List.length_map,ht]
       unfold buoy at hp; have hh : ∀ (n:ℕ)(f':View σ→ℝ)(u:View σ)(Y:List (View σ))(i:Fin n→View σ),Y=List.ofFn i→ ContDiffAt ℝ n f' u→ roc f' Y u=iteratedFDeriv ℝ n f' u i:=by
           intro n f' u Y i hi hx; have hh : Y.length=n:=by rw [hi,List.length_ofFn]
           rw [rod n Y u hx hh.le]
           subst n; congr 1; apply List.ofFn_injective; rw [List.ofFn_get]; exact hi --]
       rw [hh m W v _ (fun i=>Uniform.bolt (k i)) (by simp [l,Function.comp_def]) ((blockTaylor_contDiff ..).contDiffAt)] at hp; exact hp
    ext v'; change H v'=0; let g(i:Fin m)(u:σ):=v' i u • Uniform.bolt u; have hh:v'= fun i=>∑ x:σ,g i x:=funext fun i=> spiral _
    rw [hh,H.map_sum g]; refine sum_eq_zero (fun i _=>?_); unfold g; rw [H.map_smul_univ (fun j=>v' j (i j)) (fun j=> Uniform.bolt (i j)), he,smul_zero]
lemma permit (hm:p+1 ≤ m)(hf:∀ i:View σ,‖i‖ < r→ Allows m f i B) {x:View σ}(hx:‖x‖ < r) : ∀ n ≤ m, ‖iteratedFDeriv ℝ n (f-blockTaylor p f) x‖ ≤ B*‖x‖^(p+1-n):=by
   have hE:‖(0:View σ)‖<r:=(norm_zero (E:=View σ)).trans_lt ((norm_nonneg _).trans_lt hx); have hz':0≤B:=(hf _ hx).nonneg
   let ν:=‖x‖; let V:= f-W; let Z:=Metric.closedBall (0:View σ) ν
   have hp(j:ℕ)(hj:j≤ m)(x:View σ)(he:‖x‖<r)(h:p<j): ‖iteratedFDeriv ℝ j (f-W) x‖ ≤ B:=by rw [iteratedFDeriv_sub_apply ((hf _ he).1.of_le le_top) ((blockTaylor_contDiff ..).contDiffAt),depart x h,sub_zero]; exact (hf _ he).2 _ hj
   intro i hi; by_cases h:p< i; rw [Nat.sub_eq_zero_of_le h,pow_zero,mul_one]; exact hp _ hi _ hx h
   have hF(y:View σ)(hx:y∈Z): ‖y‖ ≤ν:= mem_closedBall_zero_iff.mp hx
   have hK(i:ℕ)(hi:i≤p+1)(y:View σ)(h:y∈ Z):‖A! i V y‖ ≤ B*ν^(p+1-i):=by
        induction hi using Nat.decreasingInduction generalizing y with
        | self=>rw [Nat.sub_self,pow_zero,mul_one]; exact hp _ hm _ ((hF _ h).trans_lt hx) (by omega)
        | of_succ i hi ih=>
           let T:= iteratedFDeriv ℝ i V; have hv(z:View σ)(hh:z∈Z): DifferentiableAt ℝ T z:= ((hf z ((hF _ hh).trans_lt hx)).1.sub ((blockTaylor_contDiff ..).contDiffAt)).differentiableAt_iteratedFDeriv (by simp)
           have hA:= (convex_closedBall (0:View σ) ν).norm_image_sub_le_of_norm_fderiv_le hv (fun z he =>(show ‖fderiv ℝ T z‖ ≤ B*ν^(p+1-(i+1)) from (by have hh:= ih z he; rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,LinearIsometryEquiv.norm_map] at hh; exact hh))) (mem_closedBall_self (norm_nonneg _)) h
           have he : T 0=0:=by unfold T V; rw [iteratedFDeriv_sub_apply ((hf _ hE).1.of_le le_top) ((blockTaylor_contDiff ..).contDiffAt), blockTaylor_jets ((hf _ hE).1.of_le le_top) i (by omega),sub_self]
           rw [he, sub_zero,sub_zero] at hA; exact hA.trans ((mul_le_mul_of_nonneg_left (hF _ h) (by positivity)).trans_eq (by rw [show p+1-i=p+1-(i+1)+1 from (by omega),pow_succ,mul_assoc]))
   exact hK _ (by omega) _ (mem_closedBall_zero_iff.mpr le_rfl)
end YM.MSbar.Bout
