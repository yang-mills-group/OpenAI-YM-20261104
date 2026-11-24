import YM.WilsonCoeffUV.Stable.Fruit
/-! # Prices via weighted moments. Orientation and exposures. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank
open Soil
open scoped Topology BigOperators
variable {L:Side}{U α β V W ι : Type*}{k r u j:ℕ} {A B s σ η : ℝ}

lemma tread_perm (p:Cover)(x:dock Cover α r)(s:Equiv.Perm (Fin r)): tread Bank.terrain p (x ∘ s)=tread Bank.terrain p x:=by
  let T: Equiv.Perm (Fin (r+1)):= ((finSuccEquiv r).trans (Equiv.optionCongr s)).trans (finSuccEquiv r).symm
  unfold tread stud; rw [← league_equiv Bank.terrain (Fin.cons p (Prod.fst ∘ x)) T]
  congr 1; funext i; refine Fin.cases (by simp [T]) (fun j=> by simp [T]) i

lemma shareS (L:Side)(i b m:ℕ)(h:L.val*i ≤ b+8*L.val)(p:0≤η)(q:η≤1) : autumn η m i≤9^m*autumn (η/L.val) m b:=by
   have ht:0<(L.val:ℝ):=by positivity
   have he : (L.val:ℝ)*i≤ b+8*L.val:= by exact_mod_cast h
   unfold autumn; rw [←mul_pow]; gcongr; field_simp; linarith only [mul_le_mul_of_nonneg_left he p,mul_le_mul_of_nonneg_right q ht.le,show 0≤ η*(b:ℝ) by positivity]
lemma share_hearth (o:Cover)(w:Site L)(p:0≤ η)(q:η≤1)(u:ℕ)(x:dock Cover (Co L α) r): hedge o η u x ≤ 9^u*hedge (L.val • o+lift w) (η/L.val) u (panel L α ∘ x):= shareS _ _ _ _ (hearth o w x) p q
lemma row_fold (f:ι→ℕ)(e:Finset ι)(h:0≤η)(u): autumn η u (∑ i∈e, f i)≤ ∏ i∈e,autumn η u (f i):=by
    classical
    induction e using Finset.induction_on with
    | empty=> simp [autumn]
    | insert i e g ih=> rw [Finset.sum_insert g,Finset.prod_insert g]; exact (autumn_tax h ..).trans (mul_le_mul_of_nonneg_left ih (zero_le_one.trans (autumn_pos h ..)))
lemma acrossRows (o:Cover)(x:dock Cover β r)(y:dock Cover α r)(h:0≤η)(u): hedge o η u x ≤ hedge o η u y * ∏ i,autumn η u (Bank.terrain.gap (y i).1 (x i).1):=by
    refine (autumn_mono h u ((prior_bit x y).trans (across Bank.terrain o x y))).trans ((autumn_tax h ..).trans ?_)
    exact mul_le_mul_of_nonneg_left (row_fold _ _ h _) (zero_le_one.trans (autumn_pos h ..))

def tender (α: Type*)[Fintype α](s:ℝ)(u:ℕ) := ceilPoly u (s/2)*boardPay α (s/2)
lemma tender_nn (p:0<s)(α:Type*)[Fintype α](u):0≤ tender α s u:= mul_nonneg (ceilPoly_pos ..).le (boardPay_nn (by positivity))
lemma tender_finance [Fintype α]{F:Cloth α→ℝ} (o:Cover) (hs:0<s)(ha:0≤A)(p:∀ x,‖F x‖≤ A*Real.exp (-s*Bank.terrain.gap o x.1))(he:0≤η)(hu:η≤1)(u:ℕ): SumBudget (fun i=> autumn η u (Bank.terrain.gap o i.1)* ‖F i‖) (A*tender α s u):=by
    set B:=ceilPoly u (s/2); have hb:0<B:= ceilPoly_pos ..
    have ht:= cap_scale (keys_cost (α:=α) o (show 0<s/2 by linarith)) (show 0≤A*B by positivity)
    unfold tender; rw [←mul_assoc]; apply budget_minor ht (fun i=>mul_nonneg (zero_le_one.trans (autumn_pos he ..)) (norm_nonneg _)); intro i
    set n:= Bank.terrain.gap o i.1; apply (mul_le_mul (autumn_shrink he hu u n) (p i) (norm_nonneg _) (zero_le_one.trans (autumn_pos zero_le_one ..))).trans; unfold autumn; rw [one_mul,mul_left_comm, mul_assoc]; apply mul_le_mul_of_nonneg_left _ ha
    have hh:= poly_used u (show s/2<s by linarith) n; rw [sub_half] at hh; exact hh

variable [NormedAddCommGroup V]{o:Cover} {P Q : Ten V (Cloth α) r}
lemma Fruit.spin (p:Fruit o η u P A)(j:Equiv.Perm (Fin r)): Fruit o η u (fun x=>P (x ∘ j)) A:= Award.pivot p (j.symm.arrowCongr (Equiv.refl (Cloth α))) rfl (funext fun (i:dock Cover α r)=> congr_arg (autumn η u) (tread_perm o i j))
lemma Fruit.turn (p:Fruit o η u P A)(v:Cover): Fruit (v+o) η u (revolve v P) A:= Award.pivot p ((Equiv.refl _).arrowCongr (jog (-v))) rfl (funext fun (i:dock Cover α r)=> congr_arg (autumn η u) (rev_league v (fun x y=>by simp [Bank.terrain]) o i).symm)
lemma Fruit.panel {o:Cover}{w:Site L}(h:Fruit (L.val • o+lift w) (η/L.val) u P A)(p:0≤η)(q:η≤1) : Fruit o η u (turnTen (panel L α).symm P) (9^u*A):=by
    let s (x:dock Cover α r):= hedge (L.val • o+lift w) (η/L.val) u x; let T:=turnTen (Bank.panel L α).symm P; let b: (dock Cover (Co L α) r)≃(Fin r→Cloth α):=(Equiv.refl _).arrowCongr (Bank.panel L α)
    have he: Award T (s ∘ b) A:= Award.pivot h b rfl rfl
    apply budget_minor (cap_scale he (show 0≤(9:ℝ)^u by positivity)) (fun x=>mul_nonneg (hedge_nn p x) (norm_nonneg _)) (fun x=>(mul_le_mul_of_nonneg_right (share_hearth o w p q u x) (norm_nonneg _)).trans_eq (by rw [mul_assoc]; rfl))
variable [NormedSpace ℝ V]
lemma Fruit.swirl (p:Fruit o η u P A)(h:0≤η):Fruit o η u (swirl P) A:=by
    let C:ℝ:= Fintype.card (Equiv.Perm (Fin r)); have hp:0<C:=by unfold C; positivity
    have ht:= (Fruit.sum (S:=Finset.univ) (fun i _=> p.spin i) h).μ C⁻¹; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,abs_of_pos (show 0<C⁻¹ by positivity)] at ht; change Fruit o η u (Blue.swirl P) (C⁻¹*(C*A)) at ht; rwa [inv_mul_cancel_left₀ hp.ne'] at ht

section
variable [Fintype β]
lemma ribbons (o:Cover)(x: dock Cover α r) (c:ℝ)(p:0<s)(Q:Fin r→ ropes Cover α β)(K:Fin r→ℝ)(h:∀ i, dragCup Bank.terrain s (K i) (Q i))(he:0≤η)(hu:η≤1) (u:ℕ): SumBudget (fun y:dock Cover β r=> hedge o η u y * ‖(∏ i,Q i (x i) (y i))*c‖) (((∏ i,K i*tender β s u)*hedge o η u x)*‖c‖):=by
    let f i (v:Cloth β):=autumn η u (Bank.terrain.gap (x i).1 v.1)*‖Q i (x i) v‖
    have hv i: SumBudget (f i) (K i*tender β s u):= tender_finance _ p (h i).1 ((h i).2 _) he hu u
    rw [mul_assoc,mul_comm]; let H:=hedge o η u x
    have hk:= cap_scale (each_finance hv) (show 0≤ H*‖c‖ from mul_nonneg (zero_le_one.trans (autumn_pos he ..)) (norm_nonneg _))
    apply budget_minor hk (fun y=> mul_nonneg (zero_le_one.trans (autumn_pos he ..)) (norm_nonneg _)); intro y
    refine (mul_le_mul_of_nonneg_right (acrossRows o y x he u) (norm_nonneg _)).trans_eq ?_
    unfold f; rw [norm_mul,norm_prod,Finset.prod_mul_distrib]; unfold H; ring
lemma ribbon_local (p:0<s)(Q: Fin r→ ropes Cover α β)(K:Fin r→ℝ)(h:∀ i,dragCup Bank.terrain s (K i) (Q i))(_Y: Fruit o η u P A)(he:0≤η)(hq:η≤1) (x:dock Cover α r): SumBudget (fun y:dock Cover β r=> hedge o η u y * ‖ribbon Q P y x‖) ((∏ i,K i*tender β s u) * (hedge o η u x*‖P x‖)):=by
    have := ribbons o x ‖P x‖ p Q K h he hq u
    simpa only [ribbon,norm_smul,norm_mul,norm_norm,mul_assoc] using this
lemma ribbon_finance (p:0<s)(Q: Fin r→ ropes Cover α β)(K:Fin r→ℝ)(h:∀ i,dragCup Bank.terrain s (K i) (Q i))(Y: Fruit o η u P A)(he:0≤η)(hq:η≤1): Award (fun i:dock Cover β r×dock Cover α r=> ribbon Q P i.1 i.2) (fun i=>hedge o η u i.1) ((∏ i,K i*tender β s u) * A):=by
    exact finance_flip (finance_glob (ribbon_local p Q K h Y he hq) (cap_scale Y (Finset.prod_nonneg fun i _=> mul_nonneg (h i).1 (tender_nn p ..))))
lemma Fruit.ribbons (G:Fin r→ ropes Cover α β)(p:0<s) (K:Fin r→ℝ) (h:∀ i,dragCup Bank.terrain s (K i) (G i))(Y:Fruit o η u P A) (he:0≤η)(hu:η≤1): Fruit o η u (ruins (ribbon G P)) ((∏ i, (K i*tender β s u))*A):= Award.cell (f:=ribbon G P) (ribbon_finance p G K h Y he hu) (fun _=> autumn_pos he ..)
lemma roses {w:Site L}(G:Fin r→ ropes Cover (Co L α) β)(p:0<s) (K:Fin r→ℝ) (h:∀ i,dragCup Bank.terrain s (K i) (G i))(Y:Fruit (L.val • o+ lift w) (η/L.val) u P A) (he:0≤η)(hu:η≤1): Fruit o η u (pump P (fun i=> owns L (G i) i)) ((∏ i,K i*tender β s u)*(9^u*A)):=by
    rw [patrol (L:=L),brush_spunk]; exact Fruit.ribbons _ p K h (Y.panel he hu) he hu
lemma pump_fin {w:Site L}(G:Fin r→ ropes Cover (Co L α) β)(p:0<s)(h:∀ i,dragCup Bank.terrain s B (G i))(Y:Fruit (L.val • o +lift w) (η/L.val) u P A)(he:0≤η)(hu:η≤1)(x): Summable fun y=>‖spinJob P (fun i=> owns L (G i) i) x y‖:=by
   let Q:= (Equiv.refl (Fin r)).arrowCongr (panel L α); apply Q.summable_iff.mp
   let T:= spunk L P (fun i=> owns L (G i) i); have H : Award (fun i:dock Cover β r × dock Cover (Co L α) r=>T i.1 i.2) (fun i=>hedge o η u i.1) ((∏ _ : Fin r, B*tender β s u)*(9^u*A)):= by simp_rw [T, brush_spunk]; exact ribbon_finance p G (fun _=>B) h (Y.panel he hu) he hu
   exact ((summable_prod_of_nonneg (fun i=>norm_nonneg (T i.1 i.2))).mp (H.sumnorm (fun _=> autumn_pos he ..))).1 x
end
end YM.WilsonCoeffUV.Shard
