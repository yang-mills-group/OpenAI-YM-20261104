import YM.WilsonCoeffUV.Thermo.VacuumCalculus
/-!
# Distinguished physical root pinned ledger & summation (including rank zero)
Root-type at every rank. Amber suffices for estimates via adding a passive root
but ports must carry the root separately in every bilinear op. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.WilsonCoeffUV.Soil
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank
open scoped Topology BigOperators
variable {n:Side}{U α β V ι E : Type*}{k r:ℕ} {A B σ η : ℝ} {d:Distance U}{c:U}{p:Cover}

abbrev stud (p:U)(x:dock U β r): Fin (r+1) → U:= Fin.cons p (Prod.fst ∘ x)
def tread (d:Distance U)(p:U)(x:dock U β r) := league d (stud p x)
def brims (d:Distance U)(p:U)(x:dock U β r)(y:dock U α k) := league d (Sum.elim (stud p x) (Prod.fst ∘ y))
lemma nth_bit (x:dock U β r)(y:dock U α k)(i): d.gap c (y i).1 ≤ brims d c x y:=leg_le d (Sum.elim (stud c x) (Prod.fst ∘ y)) (Sum.inl 0) (Sum.inr i)
lemma prior_bit (x:dock U β r)(y:dock U α k): tread d c x≤brims d c x y:= league_le d _ fun i j=>leg_le d (Sum.elim (stud c x) (Prod.fst ∘ y)) (Sum.inl i) (Sum.inl j)
lemma step_track (z:Fin r→Cover)(x:Fin r→α): (Prod.fst ∘ fun i:Fin r=> (z i,x i))=z:= rfl
lemma seen (p:Cover)(x:dock Cover α r): ∀ᶠ n:Side in atTop,tread (tor n) (wrap n p) (slideC n x)=tread Bank.terrain p x:=by
    let y:=fun i:Fin (r+1)=> (stud p x i, (():Unit))
    filter_upwards [touched y] with n hn; unfold tread
    refine Eq.trans (congr_arg (league _) ?_) hn; exact comps_head p (wrap n)

variable [NormedAddCommGroup V]
def Cork (d:Distance U)(p:U)(s C:ℝ)(F:Ten V (U×α) r): Prop:=0≤C∧∀ x, ‖F x‖≤ C*Real.exp (-s*tread d p x)
structure Bends (p:Cover)(P:raw α V r)(F:Ten V (Cloth α) r): Prop where
   point (x) : Tendsto (fun n=> P n (slideC n x)) atTop (𝓝 (F x))
   price : ∃ s C,0<s∧∀ᶠ n in atTop,Cork (tor n) (wrap n p) s C (P n)

def Peb (d:Distance U)(p:U)(s C:ℝ)(F:canal U α β V k r): Prop:= 0≤C∧∀ x y, ‖F x y‖≤ C* Real.exp (-s*brims d p x y)
structure Paves (p:Cover)(P:berth α β V k r)(F:canal Cover α β V k r): Prop where
   point (x y) : Tendsto (fun n=>P n (slideC n x) (slideC n y)) atTop (𝓝 (F x y))
   price : ∃ s C,0<s∧∀ᶠ n in atTop,Peb (tor n) (wrap n p) s C (P n)

lemma Cork.cost {P:Ten V (U×α) r} (h:Cork d c σ A P)(he:A≤B): Cork d c σ B P:= ⟨h.1.trans he,fun x=>(h.2 x).trans (mul_le_mul_of_nonneg_right he (by positivity))⟩
lemma Cork.mono {P:Ten V (U×α) r}(h:Cork d c σ A P)(hp:η≤σ): Cork d c η A P:=⟨h.1,fun x=>(h.2 x).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg hp) (by positivity))) h.1)⟩
lemma Cork.add {P Q:Ten V (U×α) r}(h:Cork d c σ A P)(g:Cork d c σ B Q): Cork d c σ (A+B) (P+Q):=⟨add_nonneg h.1 g.1,fun x=>(norm_add_le ..).trans ((add_le_add (h.2 x) (g.2 x)).trans_eq (by ring))⟩
lemma Cork.neg {P:Ten V (U×α) r}(h:Cork d c σ A P): Cork d c σ A (-P):=⟨h.1,fun x=>by rw [Pi.neg_apply,norm_neg]; exact h.2 x⟩
lemma Cork.sub {P Q:Ten V (U×α) r}(h:Cork d c σ A P)(g:Cork d c σ B Q): Cork d c σ (A+B) (P-Q):=by rw [sub_eq_add_neg]; exact h.add g.neg
lemma Cork.μ [NormedSpace ℝ V] {P:Ten V (U×α) r}(h:Cork d c σ A P)(a:ℝ): Cork d c σ (|a| *A) (a•P):=⟨mul_nonneg (abs_nonneg _) h.1, fun x=>(norm_smul a (P x)).le.trans ((mul_le_mul_of_nonneg_left (h.2 x) (norm_nonneg _)).trans_eq (by rw [mul_assoc]; rfl))⟩
lemma Cork.zero : Cork d c σ 0 (0:Ten V (U×α) r):=by simp [Cork]
lemma Cork.sum {s:Finset ι}{P:ι→Ten V (U×α) r}{M:ι→ℝ}(h:∀ i∈s,Cork d c σ (M i) (P i)): Cork d c σ (∑ i∈s,M i) (∑ i∈s,P i):=by
  classical
  induction s using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact Cork.zero
  | @insert i s e H=> rw [Finset.sum_insert e,Finset.sum_insert e]; exact (h i (Finset.mem_insert_self ..)).add (H fun j hj=>h j (Finset.mem_insert_of_mem hj))
lemma Peb.add {P Q:canal U α β V k r}(h:Peb d c σ A P)(g:Peb d c σ B Q): Peb d c σ (A+B) (P+Q):=⟨add_nonneg h.1 g.1,fun x y=>(norm_add_le ..).trans ((add_le_add (h.2 x y) (g.2 x y)).trans_eq (by ring))⟩
lemma Peb.μ [NormedSpace ℝ V] {P:canal U α β V k r}(h:Peb d c σ A P)(a:ℝ): Peb d c σ (|a| *A) (a•P):=⟨mul_nonneg (abs_nonneg _) h.1,fun x y=>(norm_smul a (P x y)).le.trans ((mul_le_mul_of_nonneg_left (h.2 x y) (norm_nonneg _)).trans_eq (by rw [mul_assoc]; rfl))⟩
lemma Peb.zero : Peb d c σ 0 (0:canal U α β V k r):=by simp [Peb]
lemma Peb.sum {s:Finset ι}{P:ι→canal U α β V k r}{M:ι→ℝ}(h:∀ i∈s,Peb d c σ (M i) (P i)): Peb d c σ (∑ i∈s,M i) (∑ i∈s,P i):=by
   classical
   induction s using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact Peb.zero
   | @insert i s e H=> rw [Finset.sum_insert e,Finset.sum_insert e]; exact (h i (Finset.mem_insert_self ..)).add (H fun j hj=>h j (Finset.mem_insert_of_mem hj))

variable {P Q:raw α V r}{T R:Ten V (Cloth α) r}
lemma Bends.land (h:Bends p P T): ∃ s A,0<s ∧ Cork Bank.terrain p s A T:= by
    obtain ⟨s,a,he,H⟩:= h.price; obtain ⟨n,hn⟩:=H.exists
    refine ⟨s,a,he,hn.1,fun x=>le_of_tendsto (h.point x).norm ?_⟩
    filter_upwards [H,seen p x] with n hn hp; rw [← hp]; exact hn.2 _
lemma Bends.congr (h:Bends p P T) (e:∀ᶠ n in atTop,P n=Q n): Bends p Q T:=by
    obtain ⟨s,a,hs,H⟩:=h.price; exact ⟨fun x=>(h.point x).congr' (e.mono fun n hn=>congr_fun hn _),s,a,hs,(e.and H).mono fun n ⟨he,hp⟩=>he ▸ hp⟩
lemma Bends.exten (h:Bends p P T)(g:Bends p P R):T=R:= funext fun x=>tendsto_nhds_unique (h.point x) (g.point x)
lemma Bends.zero:Bends p (0:raw α V r) 0:=⟨fun _=> tendsto_const_nhds,1,0,one_pos,Eventually.of_forall fun _=>Cork.zero⟩
lemma Bends.add (h:Bends p P T)(g:Bends p Q R): Bends p (P+Q) (T+R):=by
   obtain ⟨s,a,hs,H⟩:=h.price; obtain ⟨t,c,ht,J⟩:=g.price; exact ⟨fun x=>(h.point x).add (g.point x),min s t,a+c,lt_min hs ht,(H.and J).mono fun n ⟨h,t⟩=> (h.mono (min_le_left ..)).add (t.mono (min_le_right ..))⟩
lemma Bends.μ [NormedSpace ℝ V] (h:Bends p P T)(a:ℝ): Bends p (a•P) (a•T):=by
   obtain ⟨s,c,hs,H⟩:=h.price; exact ⟨fun x=>tendsto_const_nhds.smul (h.point x),s,|a| *c,hs,H.mono fun n hn=>hn.μ a⟩
lemma Bends.sub (h:Bends p P T)(g:Bends p Q R): Bends p (P-Q) (T-R):=by
   obtain ⟨s,a,hs,H⟩:=h.price; obtain ⟨t,c,ht,J⟩:=g.price; exact ⟨fun x=> (h.point x).sub (g.point x),min s t,a+c,lt_min hs ht,(H.and J).mono fun n ⟨h,t⟩=>(h.mono (min_le_left ..)).sub (t.mono (min_le_right ..))⟩
lemma Bends.sum {s:Finset ι}{P:ι→ raw α V r}{T:ι→ Ten V (Cloth α) r}(h:∀ i∈s,Bends p (P i) (T i)): Bends p (∑ i∈s,P i) (∑ i∈s,T i):=by
   classical
   induction s using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact Bends.zero
   | @insert i s e H=> rw [Finset.sum_insert e,Finset.sum_insert e]; exact (h i (Finset.mem_insert_self ..)).add (H fun j hj=>h j (Finset.mem_insert_of_mem hj))
lemma Bends.pure (h:Bends p P T)(he:∀ᶠ n in atTop,Smooth (P n)): Smooth T:= by
    intro q x; apply tendsto_nhds_unique (h.point _); exact (h.point x).congr' (he.mono fun n hn => (hn q (slideC n x)).symm)

-- carrier of bills. always has usable passive root.
def ruins (F:canal Cover α β V k r) : Ten V (Cloth β) r:= fun x=>∑' y,F x y
def refuge [Fintype α](F:canal (Site n) α β V k r) : Ten V (Co n β) r:= fun x=>∑ y,F x y
lemma Peb.stew {F:canal U α β V k r}(h:Peb d c σ A F)(he:η<σ)(hx:0≤η)(hm:0<k)(x y) : ‖F x y‖≤ A*Real.exp (-η*tread d c x)*sail ((σ-η)/k) d c y:=by rw [mul_assoc]; exact (h.2 x y).trans (mul_le_mul_of_nonneg_left (sail_cut (prior_bit x y) hx he hm _ _ (nth_bit x y)) h.1)
variable {F H:canal Cover α β V k r}{J:berth α β V k r}
variable [Fintype α]
lemma Peb.cache (h:Peb Bank.terrain p σ A F)(he:η<σ)(hx:0≤η)(x) : SumBudget (fun y=> ‖F x y‖) (A*tiePay α k (σ-η)*Real.exp (-η*tread Bank.terrain p x)):=by
    cases k with
    | zero=>
       have he' : tread Bank.terrain p x≤brims Bank.terrain p x (default:dock Cover α 0):= prior_bit ..
       refine ⟨fun _=> norm_nonneg _,summable_of_hasFiniteSupport (Set.toFinite _),?_⟩; rw [tsum_fintype,Fintype.sum_unique]; simp only [tiePay,pow_zero,mul_one]
       refine (h.2 ..).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) h.1)
       exact le_trans (mul_le_mul_of_nonneg_right (neg_le_neg he.le) (by positivity)) (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr he') (by linarith))
    | succ k=> rw [mul_right_comm]; exact budget_minor (cap_scale (train_pay (show 0<(σ-η)/(k+1:ℕ) by exact div_pos (sub_pos.mpr he) (by positivity)) _ _) (mul_nonneg h.1 (by positivity : 0≤Real.exp _))) (fun _=>norm_nonneg _) (h.stew he hx (by omega) x)
lemma Peb.meter (h:Peb Bank.terrain p σ A F)(he:η<σ)(hx:0≤η) : Cork Bank.terrain p η (A*tiePay α k (σ-η)) (ruins F):=by
    refine ⟨mul_nonneg h.1 ?_,fun x=> (norm_tsum_le_tsum_norm (h.cache he hx x).2.1).trans (h.cache he hx x).2.2⟩
    cases k with
    | zero=> rw [tiePay,pow_zero]; norm_num
    | succ k=> exact pow_nonneg (boardPay_nn (div_pos (sub_pos.mpr he) (by positivity))) _
lemma Peb.ledger {c':Site n} {F:canal (Site n) α β V k r}(h:Peb (tor n) c' σ A F)(he:η<σ)(hx:0≤η) : Cork (tor n) c' η (A*tiePay α k (σ-η)) (refuge F):=by
    cases k with
    | zero=>
       rw [tiePay,pow_zero,mul_one]; refine ⟨h.1,fun x=>?_⟩; rw [refuge,Fintype.sum_unique]
       apply (h.2 x default).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) h.1); exact le_trans (mul_le_mul_of_nonneg_right (neg_le_neg he.le) (by positivity)) (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (prior_bit ..)) (by linarith))
    | succ k=>
       have hp:0<(σ-η)/(k+1:ℕ):=div_pos (sub_pos.mpr he) (by positivity)
       refine ⟨mul_nonneg h.1 (pow_nonneg (boardPay_nn hp) _),fun x=>(norm_sum_le ..).trans ((Finset.sum_le_sum fun y _=> h.stew he hx (by omega) x y).trans ?_)⟩
       rw [← Finset.mul_sum,mul_right_comm A (tiePay α _ _)]; exact mul_le_mul_of_nonneg_left (train_native hp _ _) (mul_nonneg h.1 (by positivity))
variable [CompleteSpace V]
lemma Peb.minus (h:Peb Bank.terrain p σ A F)(e:Peb Bank.terrain p σ B H)(he:0<σ): ruins (F-H)=ruins F-ruins H:=funext fun x=> Summable.tsum_sub (h.cache he le_rfl x).2.1.of_norm (e.cache he le_rfl x).2.1.of_norm
lemma Paves.rest (h:Paves p J F): Bends p (fun n=> refuge (J n)) (ruins F):=by
    classical
    obtain ⟨s,a,hs,H⟩:= h.price; set t:=s/2; have hp:0<t:= by unfold t; positivity
    have ht:t<s:= by unfold t; linarith
    refine ⟨fun x=>?_,t,_,hp,H.mono (fun _ hn=>hn.ledger ht hp.le)⟩
    cases k with
    | zero=> simp only [refuge,Fintype.sum_unique,ruins,tsum_fintype,Fintype.sum_unique]; exact (h.point x default).congr (fun n=> by rw [Subsingleton.elim (slideC n (_:dock Cover α 0)) default])
    | succ k=>
       let W (n:Side)(y):= if unfoldAt p (slideC n y)=y then J n (slideC n x) (slideC n y) else 0
       let c:=s/(k+1:ℕ); have hc :0<c:= by unfold c; positivity
       have hv : Tendsto (fun n=>∑' y,W n y) atTop (𝓝 (ruins F x)):=by
          refine tendsto_tsum_of_dominated_convergence (bound:=fun y=> a*sail c Bank.terrain p y) ((train_pay hc p _).2.1.mul_left a) (fun y=> (h.point x y).congr' ((slide_end p y).mono fun n hn=> Eq.symm (if_pos hn))) ?_
          filter_upwards [H] with n hn
          intro y; unfold W; split
          · rename_i hr; have he:= hn.stew hs le_rfl (by omega) (slideC n x) (slideC n y); simp only [sub_zero,neg_zero,zero_mul,Real.exp_zero,mul_one] at he; apply he.trans_eq; apply congr_arg (a*·); apply Finset.prod_congr rfl; intro i _; have hx:=near_change p (slideC n y) i; rw [hr] at hx; rw [← hx]
          rw [norm_zero]; exact mul_nonneg hn.1 (sail_nn ..)
       exact hv.congr fun n=> slip_rule p _
end YM.WilsonCoeffUV.Soil
