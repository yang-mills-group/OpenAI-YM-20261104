import YM.SchemeConversionRG11.Maxwell.IndexPole
import YM.SchemeConversionRG11.Maxwell.Loop

/-! # Two-edge terms of an actual Wick family. Include both orders of the
legs coming from a square. -/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter Maxwell Maxwell.Free Wick Tensor Set MvPolynomial
open scoped BigOperators ComplexOrder

variable {n k l : ℕ}

/-- Vertex and grade of a connected line to a fixed real vertex from one mobile square. -/
abbrev Arm (n : ℕ) := Fin n × ℕ
abbrev Arms (n : ℕ) := Arm n × Arm n

def armset (n : ℕ) (N : Fin n → ℕ) : Finset (Arm n) := ((Finset.univ : Finset (Fin n)).sigma (fun i ↦ Finset.range (N i+1))).map (Equiv.sigmaEquivProd (Fin n) ℕ).toEmbedding
lemma arm_in {N : Fin n → ℕ} {i : Arm n} : i ∈ armset n N ↔ i.2 ≤ N i.1 := by
  unfold armset; obtain ⟨i,j⟩ := i; simp [Equiv.sigmaEquivProd]
lemma arm_sum {N : Fin n → ℕ} (f : Arm n → ℂ) : ∑ i∈armset n N,f i=∑ i : Fin n, ∑ j ∈ Finset.range (N i+1), f (i,j) := by rw [armset,Finset.sum_map,Finset.sum_sigma]; rfl

variable {G : Gauge}

def chargeArm (i : Arm n) : Fin n → ℕ := fun j ↦ if j=i.1 then i.2+3 else 0

def charges (u : Arms n) := chargeArm u.1+chargeArm u.2
lemma chargeEval (x : Fin n → Space) (b : Space) (i : Arm n) : aeval b (DD x (chargeArm i))=sq (b-x i.1)^(i.2+3) := by
  unfold DD; rw [Finset.prod_eq_single_of_mem i.1 (Finset.mem_univ _)]
  · rw [map_pow,varied_at,chart_at]; unfold chargeArm; simp only [if_true]
  intro j _ hj; rw [chargeArm, if_neg hj,pow_zero]

def pay (D D' : Derivation ℂ (WickPol G) (WickPol G)) (x : Points n) (a b : Fin n) (W : Fin n → WickPol G) :=
  wield (wield (moment G x) b D'.toLinearMap) a D.toLinearMap W
lemma pay_smul (D D' : Derivation ℂ (WickPol G) (WickPol G)) (t s : ℂ) (x : Points n) (a b : Fin n) (W : Fin n→WickPol G) :
    pay (t • D) (s • D') x a b W = t*s*pay D D' x a b W := by
  let U := wield (moment G x) b (s • D').toLinearMap
  unfold pay; change wield U _ _ _ = _
  rw [wield_at]; change U (update W a (t • D (W a)))=_
  rw [MultilinearMap.map_update_smul]; unfold U; rw [wield_at]; let w := update W a (D (W a)); change t • moment G x (update w b (s • D' (w b)))=_
  rw [MultilinearMap.map_update_smul,wield_at,wield_at,mul_assoc]; rfl

def hit (D : Echo k) (i : G.ColorIndex) (a : Fin n) (W : Fin n→WickPol G) := update W a (rip D i (W a))
lemma pay_hits (D : Echo k) (E : Echo l) (i j : G.ColorIndex) (x : Points n) (a b : Fin n) (W : Fin n→WickPol G) :
    pay (rip D i) (rip E j) x a b W = moment G x (hit E j b (hit D i a W)) := by unfold pay; rw [wield_at,wield_at]; rfl

variable {ι : Type*} [Fintype ι]

/-- port carrying one color thread. no invariance hypothesis on WS. -/
def payable (x : Points n) (p : ι → ℂ) (W : ι → Fin n → WickPol G) (a b : Fin n) (D : Echo k) (E : Echo l) := ∑ i:ι, ∑ j:G.ColorIndex, p i * pay (rip D j) (rip E j) x a b (W i)
lemma pay_switch {x : Points n} (p : ι → ℂ) (W : ι → Fin n → WickPol G) (D : Echo k) (E : Echo l) {a b : Fin n} (h : a≠b) :
    payable x p W a b D E = payable x p W b a E D := by unfold payable pay; simp_rw [wield_switch (moment G x) b a h.symm]

def priceL (x : Points n) (p : ι → ℂ) (W : ι → Fin n → WickPol G) (a b : Fin n) : Echo k →ₗ[ℂ] Echo l →ₗ[ℂ] ℂ where
  toFun D :=
    { toFun E := payable x p W a b D E
      map_add' E E' := by simp_rw [payable,pay_hits,hit,rip_add,MultilinearMap.map_update_add,mul_add,Finset.sum_add_distrib]
      map_smul' s E := by simp_rw [payable,pay_hits,hit,rip_scale,MultilinearMap.map_update_smul, RingHom.id_apply,smul_eq_mul,Finset.mul_sum]; congr 1; ext1 i; apply Finset.sum_congr rfl; intro j _; rw [mul_left_comm] }
  map_add' D T := by
    ext1 E; change payable x p W _ _ _ _ = _ + _; unfold payable pay; let A j := wield (moment G x) b (rip E j).toLinearMap
    have he (i j) : pay (rip (D+T) j) (rip E j) x a b (W i)=pay (rip D j) (rip E j) x a b (W i)+pay (rip T j) (rip E j) x a b (W i) := by
      unfold pay; rw [wield_at]; change A j (update (W i) _ (rip _ _ _))= _; rw [rip_add,MultilinearMap.map_update_add]; unfold A; simp only [wield_at]; rfl
    change (∑ i:ι, ∑ j:G.ColorIndex, p i * pay _ _ _ _ _ _)=(∑ i:ι, ∑ j:G.ColorIndex, p i*pay _ _ _ _ _ (W i))+(∑ i:ι, ∑ j:G.ColorIndex,p i*pay _ _ _ _ _ (W i))
    -- avoid infer underspec
    simp_rw [he,mul_add,Finset.sum_add_distrib]
  map_smul' t D := by
    ext1 E; change payable x p W a b (t • D) E=t • payable x p W a b D E
    have he (D : Echo k) j : rip (t • D) (G:=G) j=t • rip D j := by ext1 p; exact rip_scale t D j (X p)
    unfold payable; simp only [he, smul_eq_mul, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    have hx := pay_smul (rip D j) (rip E j) t 1 x a b (W i); rw [one_smul,mul_one] at hx
    rw [hx,mul_left_comm]

lemma bilinear_arity (C₀ : G.ColorIndex) (x y : Space) (L : Echo k →ₗ[ℂ] Echo l →ₗ[ℂ] ℂ) (p : Flavor 0) :
    ∃ P : Script, ∀ b : Space, aeval b P=L (shoot C₀ k (b-x) p) (shoot C₀ l (b-y) p) := by
  classical
  refine ⟨∑ i, ∑ j, varied x (arrow C₀ p (dualCash k i)) * varied y (arrow C₀ p (dualCash l j))*
    C (L (changeNote i) (changeNote j)),?_⟩
  intro b
  simp only [map_sum,map_mul,aeval_C,Algebra.algebraMap_self,RingHom.id_apply,varied_at]
  let D := shoot C₀ k (b-x) p; let E := shoot C₀ l (b-y) p
  change _ = L D E
  conv_rhs => rw [faith D, map_sum,LinearMap.sum_apply]
  apply Finset.sum_congr rfl; intro i _
  conv_rhs => rw [map_smul,LinearMap.smul_apply]; rhs; rw [faith E,map_sum]
  rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _
  rw [map_smul,mul_assoc]; rfl

def binder (Q : Probe G 0) (x : Points n) (b : E4) (U : Fin n → WickPol G) (i : Arms n) := pay
  (singleBite i.1.2 Q (b-x i.1.1)) (singleBite i.2.2 Q (b-x i.2.1)) x i.1.1 i.2.1 U

lemma bival (Q : Probe G 0) (x : Points n) (b : E4) (hp : Points.cons b x ∈ conf _) (hx : x∈conf n) (U : Fin n → WickPol G)
    (N : Fin n → ℕ) (h : ∀ i, U i∈ shelf G (N i)) : bookend x b U (symbol 0 Q * symbol 0 Q)=
    ∑ i∈(armset n N) ×ˢ (armset n N), binder Q x b U i := by
  classical
  rw [front_egress hp hx Q Q U, Finset.sum_product]
  rw [arm_sum]; simp_rw [arm_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  let F := wield (moment G x) i (eat Q b (x i)).toLinearMap
  rw [wield_at]; change F (update U a (eat _ _ _ _))=_
  rw [all_bite Q b _ (U a) (h a),MultilinearMap.map_update_sum]; refine Finset.sum_congr rfl fun j _ ↦ ?_
  let v := update U a (singleBite j Q (b-x a) (U a))
  have hv (i) : v i ∈ shelf G (N i) := by
    rcases eq_or_ne i a with rfl|hp
    · unfold v; rw [update_self]; exact upper_shelf (h i) Q _
    unfold v; rw [update_of_ne hp]; exact h i
  unfold F; rw [wield_at]; change moment G x (update v i (eat Q b (x i) (v i)))=_
  rw [all_bite Q b _ (v i) (hv i),MultilinearMap.map_update_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_; unfold binder pay; rw [wield_at, wield_at]; rfl

lemma pairFamily (C₀ : G.ColorIndex) (u : Arms n) (x : Points n) (p : ι → ℂ) (W : ι→Fin n→WickPol G) (q : Flavor 0) :
    ∃ f : Script, (∀ b : Space, aeval b f=payable x p W u.1.1 u.2.1 (shoot C₀ u.1.2 (b-poles x u.1.1) q) (shoot C₀ u.2.2 (b-poles x u.2.1) q)) ∧
      ∀ b:E4,(∀ i,b ≠ x i) → aeval (paint b) f / aeval (paint b) (DD (poles x) (charges u)) =
        ∑ i : ι, ∑ j:G.ColorIndex,p i*binder (flavor 0 j q) x b (W i) u := by
  obtain ⟨f,h⟩ := bilinear_arity C₀ (poles x u.1.1) (poles x u.2.1)
    (priceL (k:=u.1.2) (l:=u.2.2) x p W u.1.1 u.2.1) q
  change ∀ b : Space, aeval b f=payable _ _ _ _ _ _ _ at h
  refine ⟨f,h,fun b hb ↦ ?_⟩
  have hx (i) : paint b-poles x i=paint (b-x i) := (paint_sub ..).symm
  have ht : aeval (paint b) (DD (poles x) (charges u))≠0 := DD_ne _ _ _ (fun i ↦ by rw [hx]; exact paint_separate (sub_ne_zero.mpr (hb i)))
  rw [div_eq_iff ht,h,charges,DD_add,map_mul,chargeEval,chargeEval,hx,hx]; simp only [payable,rip_fare C₀ q _ (sub_ne_zero.mpr (hb _)), pay_smul,Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; unfold binder; ring

end YM.SchemeConversionRG11.Corona
