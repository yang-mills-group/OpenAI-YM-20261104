import YM.WilsonCoeffUV.Stable.PolyTariff
/-! # Charges on wick visits. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank
open Soil
open scoped Topology BigOperators
variable {L:Side}{U α β V W ι : Type*}{i k r u j:ℕ} {A B C D F' s σ η: ℝ} {o:Cover}
private def chamber (T:Type*)(r:ℕ) : ((Fin r→T)× (Fin 2→ T)) ≃ (Fin (r+2) → T) where
   toFun x:= Fin.cons (x.2 1) (Fin.cons (x.2 0) x.1)
   invFun x:= (Fin.tail (Fin.tail x),![Fin.tail x 0,x 0])
   left_inv := fun ⟨x,y⟩=> Prod.ext (by simp) (funext fun i=>by fin_cases i<;> simp)
   right_inv x:=by simp

private def hew (x:dock Cover α (i+j)) (y:dock Cover α 2) : dock Cover α (i+1):=Fin.cons (y 0) (x ∘ Fin.castAdd j)
private def finish (x:dock Cover α (i+j))(y:dock Cover α 2) : dock Cover α (j+1):= Fin.cons (y 1) (x ∘ Fin.natAdd i)
private def clove (i j:ℕ)(α:Type*): ((dock Cover α (i+j)) × (dock Cover α 2)) ≃ ((dock Cover α (j+1)) × (dock Cover α (i+1))) where
   toFun x:= (finish x.1 x.2,hew x.1 x.2)
   invFun x:= (Fin.append (Fin.tail x.2) (Fin.tail x.1),![x.2 0,x.1 0])
   left_inv:= fun ⟨x,y⟩=> Prod.ext (funext (fun u=> Fin.addCases (fun _=>by simp [hew,finish]) (fun _=>by simp [hew,finish]) u)) (funext fun i=>by fin_cases i <;>simp [hew,finish])
   right_inv:= fun ⟨x,y⟩=>by
      dsimp [hew,finish]; congr <;>ext1 x <;>refine Fin.cases (by simp) (fun i=>by simp [Fin.tail]) x

def piped (β:Type*)[Fintype β](i:ℕ)(s:ℝ)(u:ℕ) := ceilPoly u (s/2)*tiePay β i (s/2)
lemma piped_nn [Fintype β] (i:ℕ)(p:0<s)(u:ℕ) : 0≤piped β i s u:= by
    apply mul_nonneg (ceilPoly_pos ..).le; cases i with
    | zero=> rw [tiePay,pow_zero]; norm_num
    | succ i=> exact pow_nonneg (boardPay_nn (by positivity)) _

section
variable [NormedAddCommGroup V]
lemma piped_cost [Fintype β](p:0<s)(h:0≤η)(hp:η≤1){P:Ten V (Cloth β) (i+1)}(w:Amber Bank.terrain s B P)(x:Cloth β)(u:ℕ) : SumBudget (fun y:dock Cover β i=> let m:=Fin.cons x y; autumn η u (soar Bank.terrain m) * ‖P m‖) (B*piped β i s u):= by
   have H := cent_amber w p x u; unfold cent at H; simp only [sub_zero,zero_mul,Real.exp_zero,mul_one] at H; unfold piped; rw [←mul_assoc]; apply budget_minor H (fun i=>mul_nonneg (zero_le_one.trans (autumn_pos h ..)) (norm_nonneg _)); intro i; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); simpa only [autumn,one_mul] using autumn_shrink h hp u _

def Ragtop (o:Cover)(η:ℝ)(u:ℕ)(P:canal Cover α β V k r)(A:ℝ): Prop:= Award (fun i:dock Cover β r×dock Cover α k=> P i.1 i.2) (hedge o η u ∘ Prod.fst) A
namespace Ragtop
variable {P Q:canal Cover α β V k r}
lemma epochT(p:Ragtop o η u P A)(q:A≤B): Ragtop o η u P B:= Award.more p q
lemma plus (p:Ragtop o η u P A)(q:Ragtop o η u Q B)(h:0≤η): Ragtop o η u (P+Q) (A+B):= Award.plus p q fun _=> hedge_nn h _
lemma minus (p:Ragtop o η u P A) : Ragtop o η u (-P) A:= Award.minus p
lemma diff (p:Ragtop o η u P A)(q:Ragtop o η u Q B)(h:0≤η): Ragtop o η u (P-Q) (A+B):= Award.diff p q (fun _=> hedge_nn h _)
lemma sum {S:Finset ι}{P:ι→canal Cover α β V k r}{w:ι→ℝ}(p:∀ i∈S,Ragtop o η u (P i) (w i))(h:0≤η): Ragtop o η u (∑ i∈S,P i) (∑ i∈S,w i):=by
  classical
  induction S using Finset.induction_on with
  | empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact Award.zero
  | @insert i S e ih=> rw [Finset.sum_insert e,Finset.sum_insert e]; exact (p i (Finset.mem_insert_self ..)).plus (ih fun j hj=> p j (Finset.mem_insert_of_mem hj)) h
lemma turn_f (p:Ragtop o η u P A)(i: Equiv.Perm (Fin r)): Ragtop o η u (fun x y=>P (x ∘ i) y) A:= Award.pivot p ((i.symm.arrowCongr (Equiv.refl (Cloth β))).prodCongr (Equiv.refl _)) rfl (funext fun j=>congr_arg (autumn η u) (tread_perm o j.1 i))
lemma μ [NormedSpace ℝ V](p:Ragtop o η u P A)(c:ℝ): Ragtop o η u (c•P) (|c| * A):= Award.μ p c
lemma spun [NormedSpace ℝ V]{P:canal Cover α α V 2 r}(p:Ragtop o η u P A)(h:0≤η): Ragtop o η u (swivel P) A:=by
    let C:ℝ:=Fintype.card (Equiv.Perm (Fin r)); have hc:0<C:=by unfold C; positivity
    have he:= (Ragtop.sum (S:=Finset.univ) (fun i _=> p.turn_f i) h).μ C⁻¹; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,abs_of_pos (show 0<C⁻¹ by positivity)] at he; change Ragtop o η u (swivel P) (C⁻¹*(C*A)) at he; rwa [inv_mul_cancel_left₀ hc.ne'] at he
lemma collectR (p:Ragtop o η u P A)(hp:0≤η) : Fruit o η u (ruins P) A:= Award.cell (f:=P) p (fun _=> autumn_pos hp ..)
lemma sumnorm (p:Ragtop o η u P A)(h:0≤η) (x): Summable (fun y=>‖P x y‖):= ((summable_prod_of_nonneg (fun i:dock Cover β r×dock Cover α k=> norm_nonneg (P i.1 i.2))).mp (Award.sumnorm p (fun _=>autumn_pos h ..))).1 x
lemma collect_minus [CompleteSpace V](p:Ragtop o η u P A)(q:Ragtop o η u Q B)(h:0≤η): ruins (P-Q)=ruins P-ruins Q:=funext fun x=> Summable.tsum_sub (p.sumnorm h x).of_norm (q.sumnorm h x).of_norm
end Ragtop

variable [NormedSpace ℝ V]
lemma ragRain {G:ropes Cover α α}{P: Gen V (Cloth α)} (p:∀ i j,‖G i j‖≤B) (hb:0≤B)(h:Fruit o η u (P (r+2)) A)(he:0≤η): Ragtop o η u (rain G P r) (((1/2:ℝ)*B*(r+1:ℕ)*(r+2:ℕ))*A):=by
   let K:ℝ:= 1/2*B*(r+1:ℕ)*(r+2:ℕ); have hk :0≤K:= by unfold K; positivity
   let y:= chamber (Cloth α) r; have H:= cap_scale (Award.pivot (P:=P _ ∘ y) h y rfl rfl) hk; apply budget_minor H (fun z=>mul_nonneg (hedge_nn he _) (norm_nonneg _)); intro z
   let i:= z.1; let j:=z.2
   have hx: tread Bank.terrain o i ≤ tread Bank.terrain o (y z):=(prior_bit i j).trans (tap_cup i j)
   refine (mul_le_mul_of_nonneg_right (autumn_mono he u hx) (norm_nonneg _)).trans ?_
   rw [mul_left_comm K]; apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (autumn_pos he ..))
   rw [rain_spell,norm_smul]
   exact mul_le_mul_of_nonneg_right (by simp_rw [norm_mul]; push_cast; unfold K; push_cast; simp; rw [abs_of_nonneg (show 0≤(r:ℝ)+1 by positivity),abs_of_nonneg (show 0≤(r:ℝ)+2 by positivity)]; gcongr; exact p _ _) (norm_nonneg _)

lemma ragRill [Fintype α]{P:Gen ℝ (Cloth α)}{Q:Gen V (Cloth α)} {G:ropes Cover α α}(p:0<s)(h: dragCup Bank.terrain s B G)(q:Amber Bank.terrain s A (P (i+1)))(t:Fruit o η u (Q (j+1)) D)(v:i+j=k)(he:0≤η)(hu:η≤1): Ragtop o η u (rill G P Q k i j) (((1/2:ℝ)*(i+1:ℕ)*(j+1:ℕ))*(D*(B*tender α s u*(A*piped α i s u)))):=by
   subst k; have ha:= q.1; have hb:=h.1; let R:= tender α s u; let H:=piped α i s u; let C:= (1/2:ℝ)*(i+1:ℕ)*(j+1:ℕ); have hc:0≤C:=by unfold C; positivity
   let T:=clove i j α; let X (y:dock Cover α (j+1))(x:dock Cover α (i+1)):= (autumn η u (Bank.terrain.gap (x 0).1 (y 0).1)*‖G (x 0) (y 0)‖)*(autumn η u (soar Bank.terrain x)* ‖P (i+1) x‖)
   have hx y: SumBudget (X y) (B*R*(A*H)) := by
       let f (x:Cloth α):= autumn η u (Bank.terrain.gap x.1 (y 0).1)*‖G x (y 0)‖
       have heq : SumBudget f (B*R):= by
           unfold f; simp_rw [Bank.terrain.swap _ (y 0).1]
           apply tender_finance _ p hb _ he hu u; intro x; rw [Bank.terrain.swap]; exact h.2 _ _
       exact cap_walk _ _ (Fin.consEquiv (fun _:Fin (i+1)=>Cloth α)) (fun _=>rfl) (prod_cap heq (mul_nonneg ha (piped_nn _ p _)) (fun x=>piped_cost p he hu q x u))
   have hp:= cap_scale (prod_cap t (mul_nonneg (mul_nonneg hb (tender_nn p ..)) (mul_nonneg ha (piped_nn _ p _))) hx) hc
   apply budget_minor (cap_walk _ T.symm (f:=fun x=>C*((hedge o η u (T x).1*‖Q _ (T x).1‖)*X (T x).1 (T x).2)) (fun _=> by rw [T.apply_symm_apply]) hp) (fun i=>mul_nonneg (hedge_nn he _) (norm_nonneg _))
   intro x; let a:=x.1; let b:=x.2; let m:= (i+1:ℕ); let n:= (j+1:ℕ); let y:= finish a b; let z:= hew a b
   have hh : hedge o η u a≤ autumn η u (soar Bank.terrain z)*autumn η u (Bank.terrain.gap (b 0).1 (b 1).1)*hedge o η u y := (autumn_mono he u ((prior_bit a b).trans (right_cup a b))).trans ((autumn_tax he ..).trans (mul_le_mul_of_nonneg_right (autumn_tax he ..) (zero_le_one.trans (autumn_pos he ..))))
   refine (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans_eq ?_
   change _ * ‖rill G P Q (i+j) i j a b‖ = C*((hedge o η u y* ‖Q n y‖)*X y z)
   rw [rill_spell,norm_smul]; change _* (‖1/2*G _ _*(m:ℝ)*(n:ℝ)*P m z‖ * ‖Q n y‖) = _; unfold X; change _= (1/2*(m:ℝ)*(n:ℝ))*((hedge o η u y*‖Q n y‖)*((autumn η u (Bank.terrain.gap (b 0).1 (b 1).1)*‖G (b 0) (b 1)‖)*(autumn η u (soar Bank.terrain z)*‖P m z‖)))
   simp_rw [norm_mul]; simp only [norm_div,norm_one, Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤(m:ℝ)),abs_of_nonneg (by positivity : 0≤(n:ℝ)),abs_of_nonneg (by positivity : 0≤ (2:ℝ))]; ring
end
end YM.WilsonCoeffUV.Shard
