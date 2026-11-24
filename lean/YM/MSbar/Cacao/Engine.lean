import YM.MSbar.Cacao.Heat
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Cacao
open PowerSeries Finset Function Polynomial
open scoped BigOperators Classical
variable {σ:Type}[Fintype σ]
open MvPolynomial
local notation "P"=>Pot σ
local notation "B"=>Ball σ
local notation "G"=> PowerSeries (Pot σ)
local notation "K"=> PowerSeries B
variable (k:σ→σ→ℝ)(f:PowerSeries (Pot σ))
-- Lifts linear map.Bal via polynomial coeff.Season.Limit order
noncomputable def rideP (D : Module.End ℝ (Pot σ))(f : B) :B := ∑ i∈Finset.range (f.natDegree+1), Polynomial.monomial i (D (f.coeff i))
lemma riseP (D : Module.End ℝ (Pot σ))(f : B)(i:ℕ): (rideP D f).coeff i = D (f.coeff i):=by
    unfold rideP; rw [Polynomial.finsetSum_coeff]; by_cases he:i≤ f.natDegree
    · rw [Finset.sum_eq_single_of_mem i (mem_range.mpr (by omega)),Polynomial.coeff_monomial]; simp; exact fun j _ hx=>by rw [Polynomial.coeff_monomial,if_neg hx]
    rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge he),_root_.map_zero]; refine Finset.sum_eq_zero fun j hj=>?_ ; have hh:=mem_range.mp hj; rw [Polynomial.coeff_monomial,if_neg (by omega)]
def elevatorP (D : Module.End ℝ (Pot σ)): Module.End ℝ B where
    toFun:=rideP D
    map_add' f g := Polynomial.ext fun n=> by simp_rw [riseP,Polynomial.coeff_add,_root_.map_add,riseP]
    map_smul' r v:= Polynomial.ext fun n=>by simp_rw [riseP,Polynomial.coeff_smul,map_smul,RingHom.id_apply,riseP]
lemma liftedP (D : Module.End ℝ P)(f g:B) (h: ∀ x y, D (x*y)=D x*y+x*D y):elevatorP D (f*g)= elevatorP D f*g+f*elevatorP D g:=by
   apply Polynomial.ext; intro n; change (rideP ..).coeff _= (rideP D f*g+f*rideP D g).coeff _; rw [riseP,Polynomial.coeff_mul,_root_.map_sum,Polynomial.coeff_add,Polynomial.coeff_mul,Polynomial.coeff_mul,← sum_add_distrib]; exact sum_congr rfl fun j _=>by rw [h,riseP,riseP]
abbrev low (C : K)(n i : ℕ): P := (PowerSeries.coeff n C).coeff i
def dusk (c : σ) : Module.End ℝ (Ball σ):= elevatorP ((pderiv c).toLinearMap)
local notation "CC"=> Autumn
local notation "E!"=> Spring
local notation "e!"=> elevatorP
local notation "s!" => (pearl k)
local notation "v!" => stove k
abbrev rung (j:σ): Module.End ℝ K:=pulled (dusk j)
abbrev enow (j:σ) : Module.End ℝ G:=pulled ((pderiv j).toLinearMap)
lemma dusks (j:σ)(F:K)(n i:ℕ): low ((rung j) F) n i= pderiv j (low F n i):=by rw [rung,low,ride]; exact riseP ..
lemma duskD (j:σ)(X Y:B): dusk j (X*Y)= dusk j X*Y+X*dusk j Y:=liftedP _ _ _ fun _ _=> pderiv_mul
noncomputable def Gallery : K:= PowerSeries.mk fun i=> pearl k (PowerSeries.coeff i (Spring f))
def normalized := Autumn (Gallery k f)
variable {k f}
lemma airy (h:Kind f):Kind (normalized k f) ∧ Spring (normalized k f) = Gallery k f:=by
    have hp:PowerSeries.coeff 0 (Gallery k f)=1 :=by rw [Gallery, PowerSeries.coeff_mk,covers h,stop]
    exact fall_1 hp
-- evolution & Euler identity.T.S.Density normalization.Exp heat ratio.
noncomputable def dawn : (Ball σ)→ₐ[ℝ](Pot σ) := (Polynomial.aeval (R:=Pot σ) (0:Pot σ)).restrictScalars ℝ -- aeval sigma domain ℝ. instead evalRingHom.restrictScalars
lemma opens (p:Ball σ): dawn p = p.coeff 0:=by change Polynomial.eval 0 p = _;rw [Polynomial.coeff_zero_eq_eval_zero]
variable (k)
 -- placeholder
set_option quotPrecheck false
local notation "Ht"=> (Polynomial.derivative (R:=Pot σ)).restrictScalars ℝ
lemma mounts (p:Ball σ) (n:ℕ): (Ht p).coeff n = (n+1:ℝ) • p.coeff (n+1) := by rw [show Ht p=Polynomial.derivative p from rfl,Polynomial.coeff_derivative]; push_cast; rw [Algebra.smul_def]; simp [mul_comm]
lemma topped (h:Kind f): let t :=PowerSeries.map (dawn.toRingHom) (normalized k f); t=f := by
    intro t; have hp:=airy (k:=k) h
    apply singular (by unfold Kind; unfold t; rw [PowerSeries.coeff_map,hp.1,_root_.map_zero]) h -- edit
    rw [show t=PowerSeries.map dawn.toRingHom _ from rfl,sunshine dawn,hp.2]; apply PowerSeries.ext; intro n; simp only [PowerSeries.coeff_map,Gallery,PowerSeries.coeff_mk]
    exact (opens _).trans (winter k _)
noncomputable def baking (k:σ→σ→ℝ):= pulled (elevatorP (stove k))
lemma toast (A:K)(n j:ℕ):low ((baking k) A) n j=∑ i,∑ z,(k i z/2) • (pderiv i (pderiv z (low A n j))):=by
   unfold low baking;rw [ride]; exact (riseP (stove k) _ _).trans (stokes k _)
lemma ascends (A:K): baking k A=∑ i, ∑ j, (k i j/2) • (rung i (rung j A)):=by
   apply PowerSeries.ext; intro n; apply Polynomial.ext; intro x; rw [map_sum,Polynomial.finsetSum_coeff ]; change low (baking k A) n x=_; rw [toast] -- syntax mismatch
   apply sum_congr rfl; intro i _; rw [map_sum,Polynomial.finsetSum_coeff]; apply sum_congr rfl; intro j _; rw [PowerSeries.coeff_smul,Polynomial.coeff_smul]; exact congr_arg _ ((dusks i _ _ _).trans (congr_arg (pderiv i) (dusks j _ _ _))).symm -- reverse
local notation "Χ!"=>Gallery k f
local notation "T"=>pulled (Ht)
noncomputable def chocolate (k:σ→σ→ℝ)(F:PowerSeries (Ball σ)):=∑ i,∑ j,(k i j/2) • ((rung i F)*(rung j F))
lemma burnt (W:K)(h:Kind W) : baking k (Spring W)=(baking k W+chocolate k W)* Spring W := by
   let Z:=Spring W; rw [ascends k (Spring W),ascends k W]; unfold chocolate; rw [←sum_add_distrib,sum_mul]; apply sum_congr rfl; intro i _; rw [←sum_add_distrib,sum_mul]; apply sum_congr rfl; intro j _
   have he : rung i (rung j (Spring W))=(rung i (rung j W) + rung i W * rung j W)*Z:= by
       rw [show rung j (Spring W)=rung j W*Spring W from springUp W (dusk j) (duskD j) h]; have hi:= ascent (dusk i) (duskD i) (rung j W) Z; change (pulled (dusk i)) (rung j W*Z)=_; rw [hi]
       have he' : pulled (dusk i) Z= rung i W * Z:= springUp W (dusk i) (duskD i) h; rw [he']; change rung i (rung j W)*Z+_=_; ring -- regroup
   rw [he,←smul_add,smul_mul_assoc]
lemma steamK (f:G) : T (Gallery k f) = baking k (Gallery k f):=by
   apply PowerSeries.ext; intro n; apply Polynomial.ext; intro r
   rw [ride,baking,ride,mounts,Gallery, PowerSeries.coeff_mk, nozzle]; exact (riseP (stove k) _ r).symm
lemma tick (W:K)(hf:Kind W): T (Spring W)= (T W)*Spring W:= springUp W (Ht) (fun i j=> by simp only [LinearMap.coe_restrictScalars]; rw [Polynomial.derivative_mul]) hf
lemma stirred (h : Kind f) : pulled (Ht) (normalized k f)= baking k (normalized k f) + chocolate k (normalized k f):=by
    obtain ⟨hz,hV⟩:=airy (k:=k) h; let W:= normalized k f
    have hh:= (steamK k f); rw [← hV,burnt k W hz,tick W hz] at hh
    exact (solitary W hz).mul_right_cancel hh -- edit
end YM.MSbar.Cacao
