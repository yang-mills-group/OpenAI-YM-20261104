import YM.WilsonCoeffUV.Vacuum.Gain.Pumps
/-!
# Redistributing length-share from pointwise polynomial multiplier
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{r:ℕ}{α β V :Type*}{s t t' σ B C D:ℝ}{L:Side}

def tollD (k:ℕ)(p:Grazing α r): ℝ:= (1+ soar terrain p:ℝ)^k
lemma toll_pos (p:Grazing α r)(k):0<tollD k p:=by unfold tollD; positivity
variable [NormedAddCommGroup V][NormedSpace ℝ V] {P:Ten V (Cloth α) r}

def TollF (k:ℕ)(P:Ten V (Cloth α) r): Ten V (Cloth α) r:= fun p=>tollD k p • P p
def Tolled {V:Type*}(k:ℕ)(U:Roof α V r): Roof α V r:= fun p x=> U p x / tollD k p
lemma TollF_amber (h:Amber terrain t C P)(k:ℕ)(he:t'<t): Amber terrain t' (C*ceilPoly k (t-t')) (TollF k P):= by
   have hp:= h.1; have hc:=ceilPoly_pos k (t-t')
   refine ⟨by positivity,fun x=>?_⟩; rw [TollF,norm_smul,Real.norm_eq_abs, abs_of_pos (toll_pos x k)]
   refine (mul_le_mul_of_nonneg_left (h.2 x) (toll_pos x k).le).trans ?_; rw [mul_left_comm,mul_assoc C]; exact mul_le_mul_of_nonneg_left (poly_used k he _) h.1

lemma update_prod {r:ℕ}(P:Fin r→ℝ)(i:Fin r) : ∏ j,P j=P i*∏ j∈Finset.univ.erase i,P j:= (Finset.mul_prod_erase _ P (Finset.mem_univ _)).symm
lemma spin_replace {R : Fin r→ Roof α β r} (i: Fin r) (Z:Roof α β r)(x y): spinJob P (Function.update R i Z) x y=(Z y (x i)*(∏ j∈Finset.univ.erase i,R j y (x j))) • P y:=by
    unfold spinJob; rw [update_prod _ i]; simp only [Function.update_self]; congr 2; exact Finset.prod_congr rfl fun j hj=> by rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
lemma spin_scale (R: Fin r→ Roof α β r)(i:Fin r)(x y)(k): spinJob (TollF k P) (Function.update R i (Tolled k (R i))) x y=spinJob P R x y:=by
    rw [spin_replace (P:=TollF k P), spinJob, update_prod _ i,TollF, Tolled,smul_smul]; congr 1; have hp:=toll_pos y k; field_simp

variable [Fintype α][CompleteSpace V]
omit [Fintype α] in
private lemma crankToll {R : Fin (r+1)→ Roof α β (r+1)}{i:Fin (r+1)} (hr:∀ j,j ≠ i→ sells L s B (R j)){k:ℕ}(h:sells L s D (Tolled k (R i)))(j) : sells L s (max B D) (Function.update R i (Tolled k (R i)) j):=by
  by_cases he:j=i; · rw [he,Function.update_self]; exact h.cost (le_max_right ..)
  rw [Function.update_of_ne he]; exact (hr j he).cost (le_max_left ..)
lemma chargeToll {P:Ten V (Cloth α) (r+1)}{R: Fin (r+1)→ Roof α β (r+1)}{i:Fin (r+1)}(hr:∀ j,j≠i→ sells L s B (R j)){k:ℕ}(h:sells L s D (Tolled k (R i)))(he:Amber terrain t C P)(ht:t'<t)(hp:s/L.val≤ t')(hv:0≤σ)(ha:σ<s):
     (∀ x,Summable (spinJob P R x))∧Amber terrain σ ((max B D ^(r+1)*(C*ceilPoly k (t-t')*Real.exp (8*s)))*tiePay (Co L α) (r+1) (s-σ)) (pump P R):=by
   set W:= TollF k P; let K:= Function.update R i (Tolled k (R i));
   have hw : spinJob W K=spinJob P R:= funext fun x=>funext fun y=>spin_scale ..
   have hQ : Amber terrain t' _ W:= TollF_amber he k ht
   have hh:∀ j,sells L s (max B D) (K j):= crankToll hr h
   refine ⟨fun x=>?_,?_⟩
   · rw [← hw]; exact (pump_sum hh hQ (lt_of_le_of_lt hv ha) hp x).of_norm
   have he := pump_pay hh hQ hv ha hp; simp only [Finset.prod_const, Finset.card_univ,Fintype.card_fin , show pump W K=pump P R from funext fun x=> by unfold Bank.pump; rw [hw]] at he; exact he
lemma spin_sub {P:Ten V (Cloth α) (r+1)}{R: Fin (r+1)→ Roof α β (r+1)} {i: Fin (r+1)} {S:Roof α β (r+1)} (hp:Amber terrain t C P) (ht:s/L.val≤t)(he:0<s)(hw:∀ i,sells L s B (R i))(h:sells L s B S):
    pump P (Function.update R i S)-pump P R=pump P (Function.update R i (S-R i)):=by
   let A:= Function.update R i S
   have hh:∀ i,sells L s B (A i):=by
     intro j
     by_cases he:j=i; · subst j; unfold A; rw [Function.update_self]; exact h
     unfold A; rw [Function.update_of_ne he]; exact hw j
   funext x; rw [Pi.sub_apply]; change (∑' y,spinJob P A x y)-(∑' y,spinJob P R x y)= _
   rw [← (pump_sum hh hp he ht x).of_norm.tsum_sub ((pump_sum hw hp he ht x).of_norm)]; apply tsum_congr; intro y
   rw [spin_replace (Z:=S) (R:=R), spin_replace]; rw [Pi.sub_apply,Pi.sub_apply,sub_mul,sub_smul,spinJob,update_prod _ i]
end YM.WilsonCoeffUV.Bank
