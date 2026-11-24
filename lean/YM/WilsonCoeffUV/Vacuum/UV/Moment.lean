import YM.WilsonCoeffUV.Vacuum.UV.LimitGauge
/-! True support budgets for formal exponent and all polynomial position reserves. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free Extension.UV.Linear PathCost Realm PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{n N M e m i k r b j l:ℕ}{U V W :Credit}{X α:Type*}{A B Q t s : ℝ}
-- closed form polynomial costs

def offerQ (α:Type*)[Fintype α](k r:ℕ)(A:ℝ):= (1+4*r*A)^r * (((2*(1+4*k*A))^(Fintype.card Axis) * Fintype.card α)^k)
lemma ember (he: 0<s)(h:s⁻¹≤A) (x:ℕ)(r:ℕ): (1+x:ℝ)^r ≤ (1+4*r*A)^r * Real.exp (s/4*x):=by
   by_cases H:r=0; · subst r; rw [pow_zero,pow_zero,one_mul]; exact Real.one_le_exp (by positivity)
   have hu:0< (r:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero H
   let z:=s/(4*r); have hz:0< z:= div_pos he (by positivity)
   have hx : 1+(x:ℝ)≤ (1+4*r*A)*Real.exp (z*x):= by
      rw [add_mul,one_mul]; refine add_le_add (Real.one_le_exp (by positivity)) (le_trans (b:=z⁻¹*Real.exp (z*x)) ?_ ?_)
      · rw [le_inv_mul_iff₀ hz]; linarith only [Real.add_one_le_exp (z*x)]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
       z⁻¹ = 4*r*s⁻¹ := by unfold z; field_simp
       _ ≤ _:=mul_le_mul_of_nonneg_left h (by positivity)
   refine (pow_le_pow_left₀ (by positivity) hx r).trans_eq ?_
   rw [mul_pow,←Real.exp_nat_mul]; congr 2; unfold z; field_simp
lemma tideQ [Fintype α](h:0<s)(hp:s⁻¹ ≤A): tiePay α k (s/4)≤ ((2*(1+4*k*A))^(Fintype.card Axis)*Fintype.card α)^k:=by
   by_cases H:k=0; · rw [tiePay,H,pow_zero,pow_zero]
   have hk : 0< (k:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero H
   let b:= s/4/k; have hb:0<b:= div_pos (by positivity) (by positivity)
   refine pow_le_pow_left₀ (boardPay_nn hb) (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (a:=2*((1+b)/b)) (by positivity) ?_ _) (by positivity)) _
   have hh : b⁻¹=4*k*s⁻¹:=by unfold b; field_simp
   rw [add_div,one_div,div_self hb.ne',hh]; nlinarith only [mul_le_mul_of_nonneg_left hp hk.le]
lemma rubBound [NormedAddCommGroup X][Fintype α]{F:Ten X (Cloth α) (k+1)}(h:Amber terrain s A F)(hp:0<s)(v:s⁻¹≤B)(r)(x:Cloth α): cent x F r (s/2) (A*offerQ α k r B):= by
   let Z := (1+4*r*B)^r
   have hB:0<B:=lt_of_lt_of_le (inv_pos.mpr hp) v
   have hZ:0≤Z:= by unfold Z; positivity
   let u:= s/4; have hu:0<u := by unfold u; positivity
   have hr (y:dock Cover α k): Real.exp (-u*soar terrain (Fin.cons x y)) ≤ sail (u/k) terrain x.1 y:= by
     by_cases he:k=0
     · subst k; simp [sail,soar,league,terrain]
     have he' j : terrain.gap x.1 (y j).1 ≤ soar terrain (Fin.cons x y):= leg_le terrain (Prod.fst ∘ (Fin.cons x y : Fin (k+1)→Cloth α)) 0 (Fin.succ j)
     simpa only [sub_zero,neg_zero,zero_mul,Real.exp_zero,one_mul] using sail_cut (d:=terrain) (Nat.zero_le (soar terrain (Fin.cons x y))) le_rfl hu (by omega) x.1 y he'
   have he : SumBudget (fun y:dock Cover α k=> sail (u/k) terrain x.1 y) (tiePay α k u):= by
     by_cases ht:k=0; · subst k; simp [sail,SumBudget,tiePay]; exact summable_of_hasFiniteSupport (Set.toFinite _)
     exact train_pay (div_pos hu (Nat.cast_pos.mpr (by omega))) _ _
   have hA:=h.1
   have hg: A*Z*tiePay α k u≤ A*offerQ α k r B:= by unfold Z u offerQ; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (tideQ hp v) hZ) hA
   have hf (y: dock Cover α k): let w:=Fin.cons x y; let l:=soar terrain w; (((1+l):ℝ)^r *Real.exp (s/2*l))*‖F w‖≤ A*Z*sail (u/k) terrain x.1 y:=by
     intro w l; calc
      _ ≤ (Z*Real.exp (s/4*l)*Real.exp (s/2*l))*(A*Real.exp (-s*l)):=mul_le_mul (mul_le_mul_of_nonneg_right (ember hp v l r) (by positivity)) (h.2 _) (by positivity) (by positivity)
      _ = (A*Z) * Real.exp (-u*l):=by rw [show -u*l=(s/4*l+s/2*l)+ -s*l by unfold u; ring,Real.exp_add,Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hr _) (by positivity)
   have hh: cent x F r (s/2) (A*Z*tiePay α k u) := budget_minor (cap_scale he (show 0≤ A*Z by positivity)) (fun _=>mul_nonneg (by positivity) (norm_nonneg _)) hf
   exact ⟨hh.1,hh.2.1,hh.2.2.trans hg⟩
def billingQ (α:Type*)[Fintype α](k r:ℕ): Credit:= ⟨r+ (Fintype.card Axis)*k,max 1 (offerQ α k r 1),le_max_left ..⟩
lemma offer_expands [Fintype α](h:1 ≤ A): offerQ α k r A ≤ (billingQ α k r).buy A:=by
  have hy:0≤A:=zero_le_one.trans h
  have H (r:ℕ): 1+4*r*A ≤ (1+4*r)*A:= by linarith
  let N':= Fintype.card Axis
  have he (k:ℕ)(p:ℕ): (((2*(1+4*k*A))^p*(Fintype.card α:ℝ))^k) ≤ (((2*(1+4*k))^p*(Fintype.card α:ℝ))^k*A^(p*k)):=by
      calc
       _ ≤ (((2*(1+4*k)*A)^p*(Fintype.card α:ℝ))^k):= pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith [H k]) p) (by positivity)) k
       _ = _:=by rw [mul_pow _ _ p,pow_mul,(show (2*(1+4*k))^p*A^p*(Fintype.card α:ℝ)= ((2*(1+4*k))^p*(Fintype.card α:ℝ))*A^p by ring),mul_pow]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right ..) (show 0≤ A^(r+N'*k) by positivity))
  unfold offerQ; simp_rw [mul_one]; rw [show (billingQ α k r).d=r+N'*k from rfl,pow_add,mul_mul_mul_comm,← mul_pow]
  exact mul_le_mul (pow_le_pow_left₀ (by positivity) (H _) _) (he k _) (by positivity) (by positivity)
lemma taxed [NormedAddCommGroup X][Fintype α] {F:Ten X (Cloth α) (k+1)}(h: Amber terrain s A F) (he:0<s)(v:1≤B)(p:s⁻¹≤B) (r)(x:Cloth α): cent x F r (s/2) (A*(billingQ α k r).buy B):= let H:= rubBound h he p r x; ⟨H.1,H.2.1,H.2.2.trans (mul_le_mul_of_nonneg_left (offer_expands v) h.1)⟩

structure Trunk (σ A Q:ℝ)(x:YForest G)(P F: Ten ℝ (YForest G) (k+1))(j:ℕ): Prop where
    main : cent x P j σ A
    cor : cent x F j σ A
    gap : cent x (P-F) j σ (A*Q)
lemma readyV {P F: Ten ℝ (YForest G) (k+1)}(h:PairA s A Q P F)(he:0<s)(v:1≤B)(p:s⁻¹≤B)(r)(x:YForest G): Trunk (s/2) (A*(billingQ (Hooks G) k r).buy B) Q x P F r:= ⟨taxed h.pose he v p r x, taxed h.vale he v p r x,by rw [mul_right_comm]; exact taxed h.visit he v p r x⟩
lemma releases (p:Traces G e U V i (k+1))(r:ℕ): ∃T:Credit,∀ R:Realm G e U,∀ m (h:R.anchor≤m) b N (_:m≤b) (_:b≤N) x, Trunk ((R.mint m h).σ /2) (R.cash T m) ((R.draws.S.a b/R.draws.S.a m) ^((4:ℝ)⁻¹)) x (actionW R.draws R.paid N m i (k+1)) (timeless R.draws R.paid m i (k+1)) r:=by
    refine ⟨V.prodC ((billingQ (Hooks G) k r).usingC U),fun R m h b N e t x=>?_⟩; rw [Realm.cash,Credit.products,Credit.stock_up,← trail_ratio]; exact readyV (inherited p R h e t) (R.mint m h).width (Credit.purchase _ (R.depth _ h)) (R.taxes _ h).width_bill _ _
end YM.WilsonCoeffUV.Bank
