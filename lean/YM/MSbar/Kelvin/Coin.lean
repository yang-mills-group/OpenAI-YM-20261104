import YM.MSbar.Kelvin.Rate
import YM.Push.STATIONARY_UNIFORM.Resolvent
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Kelvin
open Function Filter MeasureTheory Cacao PowerSeries Finset Whisk
open scoped Topology BigOperators Classical
open Lattice Matrix Push.Uniform
variable {ι σ τ:Type} [Fintype σ][Fintype ι][Fintype τ][DecidableEq σ] [DecidableEq ι]
    {l':ι→σ}{n:Side}{v : σ→ Site n}{k s: Matrix σ σ ℝ} {B : Matrix ι ι ℝ}
    (u : ι→σ)
variable (h:Injective u)
local notation "ι!"=> imbed u
local notation "p!"=> pinch u k
local notation "e!"=> extendM u
local notation "V"=> vanish u k
local notation "dp" =>(pinch u k)⁻¹
variable {a b c t r d f:ℝ} {N p m:ℕ}
include h
lemma route {S : Matrix ι ι ℝ} (hv:Sealed (v ∘ u) a S b)(he:0≤ b): Sealed v a (extendM u S) b:=by
   intro i j; let X:=extendM u S; by_cases hx:i∈ Set.range u ∧ j∈Set.range u
   · obtain ⟨⟨i,rfl⟩,j,rfl⟩:=hx; rw [show extendM u S _ _=_ from (congr_fun (congr_fun (embeds u h S) i) j : e! S _ _= S i j)]; exact hv i j
   rw [squeezed u (not_and_or.mp hx),abs_zero]; exact mul_nonneg he (Real.exp_pos _).le
lemma guarded (g:Charge k r) : Charge (pinch u k) r:=by
    intro w; let a:= imbed u *ᵥ w; have hC:=g a
    rw [show (∑ i,w i^2)=∑ i,a i^2 from ?_]
    swap; · simp_rw [pow_two]; change w ⬝ᵥ w = a ⬝ᵥ a
            have ht: (imbed u).transpose*ᵥ a = w:=(trimmed u a).trans (shares u h w)
            nth_rw 2 [← ht]; rw [dotProduct_mulVec,vecMul_transpose]
    rw [clipped,Matrix.mul_assoc,← mulVec_mulVec,← mulVec_mulVec,dotProduct_mulVec ,vecMul_transpose]; exact hC
variable (K: k.PosDef)
include K
lemma fence (ha:0<a)(hr:0<r)(hc: Charge k r)(hb:Sealed v a k b)(ht:Multiplicity v N)(he:0≤b) :
    Sealed v (tiltWidth N r a b) (extendM u dp) ((r/2)⁻¹):= route u h (inverse_sealed (show Sealed (v ∘ u) a p! b from fun i j=>hb _ _) hr ha (guarded u h hc) he (ht.comp h) (isUnit_iff_ne_zero.mpr (K.submatrix h|>.det_pos.ne'))) (inv_nonneg.mpr (half_pos hr).le)
omit h K
lemma ropes (r:ℝ)(h:0<r)(p:ℕ) : ∃ k:ℝ, 1≤k∧∀ n:ℕ,(1+(n:ℝ))^p≤ k*Real.exp (r*n):=by
    let f:=1/(min r 1); let y:=if p=0 then f else (p:ℝ)*f; cases p with
    | zero=> exact ⟨1,le_rfl,fun n=>by rw [pow_zero,one_mul]; exact Real.one_le_exp (mul_nonneg h.le (Nat.cast_nonneg _))⟩
    | succ p=>
       let t:ℝ:= ↑(p+1); let a:=r / t; have ht:1 ≤ t:= Nat.one_le_cast.mpr (Nat.zero_lt_succ ..); have ha:0<a:=div_pos h (zero_lt_one.trans_le ht)
       let c:=1+a⁻¹;have hc:1≤c:= le_add_of_nonneg_right (inv_nonneg.mpr ha.le); refine ⟨c^(p+1), one_le_pow₀ hc, fun n=> ?_⟩
       have hh: 1+(n:ℝ) ≤ c*(Real.exp (a*n)):=by
          have hF: (a * n+1) ≤ Real.exp (a*n):=Real.add_one_le_exp _; apply le_trans _ (mul_le_mul_of_nonneg_left hF (zero_le_one.trans hc)); have he := inv_mul_cancel₀ ha.ne'
          have hu : a*n≥ 0:= mul_nonneg ha.le (Nat.cast_nonneg _); unfold c; nlinarith only [hu, congr_arg (fun x:ℝ=>x*(n:ℝ)) he, inv_nonneg.mpr ha.le]
       have he : r*n=t*(a*n:ℝ):=by unfold a; have he:= (div_mul_cancel₀ r (show t≠0 from (zero_lt_one.trans_le ht).ne')); linear_combination -(n:ℝ)*he
       rw [he,Real.exp_nat_mul,← mul_pow]; exact pow_le_pow_left₀ (by positivity) hh _
lemma weave (hb: 0 ≤ b)(hw:Sealed v a k b)(h:Multiplicity v N)(hp:c+t<a)(ht:∀ n:ℕ,(1+(n:ℝ))^p≤ r*Real.exp (t*n)): LoopNet v c p k (r*(b*(N*countCost (a-(c+t))))) :=by
    have he:=count_pos (sub_pos.mpr hp); have hr : 0≤ r := by have hr:=ht 0; simp at hr; linarith only [hr];
    have hz(S:Matrix σ σ ℝ)(hw:Sealed v a S b)(i): ∑ j,|S i j| * liftW c p (separation (v i) (v j)) ≤ r*(b*(N*countCost (a-(c+t)))) := by
       apply le_trans (b:=r*∑ j:σ, |S i j| *Real.exp ((c+t)* separation (v i) (v j))) ?_ (mul_le_mul_of_nonneg_left (hw.weighted hb h hp i) hr); rw [Finset.mul_sum]; refine sum_le_sum fun j _=> ?_; unfold liftW; rw [mul_left_comm r]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); refine (mul_le_mul_of_nonneg_right (ht _) (Real.exp_pos _|>.le)).trans_eq ?_; rw [mul_assoc, ← Real.exp_add]; congr 2;ring
    refine ⟨mul_nonneg hr (mul_nonneg hb (mul_nonneg (by positivity) he.le)), hz k hw,fun i=>?_⟩; simp_rw [show ∀ j:σ,separation (v j) (v i)=separation (v i) (v j) from fun _=>separation_comm ..]; exact hz k.transpose hw.tran i
end YM.MSbar.Kelvin
