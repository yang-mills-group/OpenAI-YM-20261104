import YM.WilsonCoeffUV.Thermo.Tariff
/-!
# Rooting an amalgamated job

`canal`: internal k+1 slots, output r slots. No distinguished origin; permit
pinning a slot exactly when output rank zero, as this shore price emits per
site. All reduced costs pointwise; rooted-l1 after any proper shrinking.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08
open scoped Topology BigOperators
variable {n:Side}{U α β V ι : Type*}{k r:ℕ} {A B σ η : ℝ}

abbrev dock (U α:Type*)(k:ℕ) := Fin k → U×α
abbrev canal (U α β V: Type*)(k r:ℕ) := dock U β r→ dock U α k → V

variable {d:Distance U} [NormedAddCommGroup V]
def pairCup (d:Distance U)(σ A:ℝ)(F:canal U α β V k r): Prop:= 0≤A ∧ ∀ x y,‖F x y‖≤A*Real.exp (-σ*course d x y)

def mooring [AddGroup U](F:canal U α β V k r): Prop:= ∀ b:U,∀ x y,F (jog b ∘ x) (jog b ∘ y)=F x y

lemma pairCup.mono {F:canal U α β V k r}(h:pairCup d σ A F)(he:η≤σ): pairCup d η A F:=⟨h.1,fun x y=>(h.2 x y).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg he) (by positivity))) h.1)⟩
lemma pairCup.add {F P: canal U α β V k r}(h:pairCup d σ A F)(e:pairCup d σ B P): pairCup d σ (A+B) (F+P):=⟨add_nonneg h.1 e.1,fun x y=>(norm_add_le ..).trans ((add_le_add (h.2 x y) (e.2 x y)).trans_eq (by rw [add_mul]))⟩
lemma pairCup.smul [NormedSpace ℝ V] {F:canal U α β V k r}(h:pairCup d σ A F)(c:ℝ): pairCup d σ (|c| *A) (c•F):= ⟨mul_nonneg (abs_nonneg _) h.1,fun x y=>(norm_smul c (F x y)).le.trans ((mul_le_mul_of_nonneg_left (h.2 x y) (norm_nonneg c)).trans_eq (by rw [mul_assoc]; rfl))⟩
lemma pairCup.zero : pairCup d σ 0 (0:canal U α β V k r):=by simp [pairCup]
lemma pairCup.sum {s:Finset ι}{P:ι→canal U α β V k r}{M:ι→ℝ}(h:∀ i∈s,pairCup d σ (M i) (P i)): pairCup d σ (∑ i∈s,M i) (∑ i∈s,P i):=by
  classical
  induction s using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact pairCup.zero
  | @insert i s he H=> rw [Finset.sum_insert he,Finset.sum_insert he]; exact (h i (Finset.mem_insert_self ..)).add (H fun j hj=>h j (Finset.mem_insert_of_mem hj))

-- outgoing anchor.
def bearing [Zero U]{r:ℕ} : dock U β r→U := match r with
| 0=> fun _=> 0
| _+1=>fun x=>(x 0).1

def tie [DecidableEq U][Zero U](F:canal U α β V (k+1) r)(x:dock U β r)(y:dock U α (k+1)): V:= if r=0 ∧ (y 0).1 ≠ 0 then 0 else F x y

lemma shelves (d:Distance U)(x:dock U β r)(y:dock U α k) : soar d x ≤ course d x y:=league_le d _ fun i j=>leg_le d (Sum.elim (Prod.fst ∘ x) (Prod.fst ∘ y)) (Sum.inl i) (Sum.inl j)

lemma pole_cut [Zero U]{x:dock U β r}{y:dock U α (k+1)}(h:¬ (r=0 ∧ (y 0).1 ≠0))(i:Fin (k+1)): d.gap (bearing x) (y i).1≤course d x y := by
  let z:=Sum.elim (Prod.fst ∘ x) (Prod.fst ∘ y)
  have he : ∃ j, bearing x=z j := by
    cases r with
    | zero=> refine ⟨Sum.inr 0,?_⟩; have hh: (y 0).1=0:= by by_contra hz; exact h ⟨rfl,hz⟩
             exact hh.symm
    | succ=> exact ⟨Sum.inl 0,rfl⟩
  obtain ⟨t,hh⟩:=he; rw [hh]; exact leg_le d z t (Sum.inr i)
lemma tie_bound [Zero U][DecidableEq U]{F:canal U α β V (k+1) r}(h:pairCup d σ A F)(he:η<σ)(hx:0≤η) (x y): ‖tie F x y‖ ≤ (A*Real.exp (-η*soar d x))*sail ((σ-η)/(k+1:ℕ)) d (bearing x) y := by
  unfold tie; split
  · rw [norm_zero]; exact mul_nonneg (mul_nonneg h.1 (by positivity)) (sail_nn ..)
  rename_i hh; rw [mul_assoc]; exact (h.2 x y).trans (mul_le_mul_of_nonneg_left (sail_cut (shelves d x y) hx he (Nat.zero_lt_succ _) _ _ (pole_cut hh)) h.1)

variable [Fintype α]
abbrev tiePay (α:Type*) [Fintype α] (k:ℕ)(σ:ℝ) := boardPay α (σ/k)^k
lemma tie_cost {F:canal Cover α β V (k+1) r}(h:pairCup terrain σ A F)(he:η<σ)(hx:0≤η)(x) : SumBudget (fun y=>‖tie F x y‖) (A*tiePay α (k+1) (σ-η)*Real.exp (-η*soar terrain x)):=by
  rw [mul_right_comm]
  exact budget_minor (cap_scale (train_pay (show 0<(σ-η)/(k+1:ℕ) from div_pos (by linarith) (by positivity)) _ _) (mul_nonneg h.1 (by positivity : 0≤Real.exp _))) (fun _=>norm_nonneg _) (tie_bound h he hx x)
lemma tie_paid {F:canal (Site n) α β V (k+1) r}(h:pairCup (tor n) σ A F)(he:η<σ)(hx:0≤η)(x) : ∑ y, ‖tie F x y‖ ≤A*tiePay α (k+1) (σ-η)*Real.exp (-η*soar (tor n) x):=by
  refine le_trans (Finset.sum_le_sum fun y _=> tie_bound h he hx x y) ?_
  rw [← Finset.mul_sum,mul_right_comm A (tiePay α _ _)]
  apply mul_le_mul_of_nonneg_left (train_native _ _ _) (mul_nonneg h.1 (by positivity)); exact div_pos (sub_pos.mpr he) (by positivity)

def wear (F:canal (Site n) α β V (k+1) r): Ten V (Co n β) r := fun x=>∑ y,F x y

def worn (F:canal Cover α β V (k+1) r) : Ten V (Cloth β) r:= fun x=>∑' y,tie F x y

lemma north_stroll {F:canal (Site n) α β V (k+1) r}(h:mooring F) : stroll (wear F):= by
  intro b x
  unfold wear; symm
  exact Fintype.sum_equiv ((Equiv.refl _).arrowCongr (jog b)) _ _ (fun i=>(h b _ _).symm)
omit [Fintype α] in
lemma south_stroll {F:canal Cover α β V (k+1) r}(h:mooring F): stroll (worn F) := by
  intro b x
  unfold worn; rw [← ((Equiv.refl _).arrowCongr (jog (α:=α) (if r=0 then 0 else b))).tsum_eq (tie F _)]
  apply tsum_congr; intro i; unfold tie
  by_cases h':r=0
  · subst r
    have he : ((Equiv.refl (Fin _)).arrowCongr (jog (α:=α) (if 0=0 then (0:Cover) else b))) i =i:= by ext1 v; simp [jog]
    rw [he,Subsingleton.elim (jog b ∘ x) x]
  simp only [h', false_and,↓reduceIte]; exact h b x i

variable {F:(n:Side)→canal (Site n) α β V (k+1) r}
variable [NormedSpace ℝ V]
lemma dilute_wear (h:mooring (F n))(x) : dilute (fun n=>wear (F n)) n x=∑ y,tie (F n) x y:=by
  classical
  cases r with
  | succ r=> simp [dilute,tie,wear]
  | zero=>
    let A:= F n
    have he : wear A x= Fintype.card (Site n) • (∑ y,tie A x y):=by
      let f : Site n→dock (Site n) α (k+1)→V:=fun b y=>if (y 0).1=b then A x y else 0
      have hp (b:Site n): ∑ y, f b y=∑ y,tie A x y:= by
        symm; apply Fintype.sum_equiv ((Equiv.refl _).arrowCongr (jog b)); intro i
        change tie A x i = f b (jog b ∘ i)
        have H : A x (jog b ∘ i)=A x i:= by have ht := h b x i; rw [Subsingleton.elim (jog b ∘ x) x] at ht; exact ht
        unfold f; rw [H]; unfold tie; change _= if b+(i 0).1=b then _ else _
        by_cases he:(i 0).1=0 <;> simp [he]
      calc
        _ = ∑ y,∑ b : Site n,f b y := by simp [f,wear]
        _ = _ := by rw [Finset.sum_comm]; simp [hp]
    unfold dilute; rw [if_pos rfl,Pi.smul_apply]; change (Fintype.card (Site n):ℝ)⁻¹ • (wear A x)=_
    rw [he,← Nat.cast_smul_eq_nsmul (R:=ℝ), smul_smul,inv_mul_cancel₀,one_smul]; positivity

omit [NormedSpace ℝ V] in
lemma worn_amber {F:canal Cover α β V (k+1) r}(h:pairCup terrain σ A F)(hx:0≤η)(he:η<σ): Amber terrain η (A*tiePay α (k+1) (σ-η)) (worn F):=by
  have H := tie_cost h he hx
  exact ⟨mul_nonneg h.1 (pow_nonneg (boardPay_nn (div_pos (sub_pos.mpr he) (by positivity))) _),fun x=> (norm_tsum_le_tsum_norm (H x).2.1).trans (H x).2.2⟩
lemma wear_amber (h:pairCup (tor n) σ A (F n))(hm:mooring (F n))(hx:0≤η)(he:η<σ): Amber (tor n) η (A*tiePay α (k+1) (σ-η)) (dilute (fun n=>wear (F n)) n):=by
  refine ⟨mul_nonneg h.1 (pow_nonneg (boardPay_nn (div_pos (sub_pos.mpr he) (by positivity))) _),fun x=>?_⟩
  rw [dilute_wear hm]; exact (norm_sum_le ..).trans (tie_paid h he hx x)
end YM.WilsonCoeffUV.Bank
