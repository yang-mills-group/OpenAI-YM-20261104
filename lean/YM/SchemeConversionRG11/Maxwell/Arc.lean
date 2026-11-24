import YM.SchemeConversionRG11.Maxwell.Glints

/-! # A kernel sampling lemma on each fixed pair's punctured cone.

At the first primary we measure all independent derivative slots even of
high jet order. At the other primary in this test it's enough that the
chain coupling through the *same square* can be nonzero at zero derivative
order. Allows working one auxiliary vertex at a time.
-/

set_option autoImplicit false
noncomputable section

namespace YM.SchemeConversionRG11.Corona
open Function Filter Maxwell Maxwell.Free Set Complex
open MvPolynomial hiding C
open scoped Topology BigOperators ComplexOrder
variable {G : Gauge} (C : G.ColorIndex) {n k : ℕ}

def Echo (k : ℕ) := Flavor k →ₗ[ℝ] ℂ
attribute [reducible] Echo

lemma poleFare (q : Flavor 0) (p : Flavor k) : Pole (k+2+2) (fun x ↦ (fare C q p x:ℂ)) := by
  rw [show k+2+2=4+0+k by omega]
  exact (kernel_pole (flavor (G:=G) 0 C q) (flavor (G:=G) k C p)).coord Complex.ofRealCLM

def front (q : Flavor 0) (p : Flavor k) : Tensor.T E4 ℂ (k+2) := (cleared_ray (poleFare C q p)).choose

def arrow (q : Flavor 0) (p : Flavor k) := represent (front C q p)
lemma arrow_at (q : Flavor 0) (p : Flavor k) : Reads (k+2) (fun x ↦ (fare C q p x:ℂ)) (arrow C q p) :=
  (cleared_ray (poleFare C q p)).choose_spec
lemma arrow_scaling (q : Flavor 0) (p : Flavor k) : hyper (arrow C q p) (k+2) := complex_ray _

lemma arrow_add_begin (q q' : Flavor 0) (p : Flavor k) : arrow C (q+q') p=arrow C q p+arrow C q' p :=
  Reads.uniq (arrow_at C _ _) (fun x (hx : x≠0) ↦ by
    rw [map_add,arrow_at C _ _ x hx,arrow_at C _ _ x hx, ← fare_pair _ (q+q') p hx,map_add,LinearMap.add_apply,fare_pair,fare_pair, ofReal_add]; ring)
lemma arrow_add (q : Flavor 0) (p p' : Flavor k) : arrow C q (p+p')=arrow C q p+arrow C q p' :=
  Reads.uniq (arrow_at C _ _) (fun x (hx : x≠0) ↦ by
    rw [map_add,arrow_at C _ _ x hx,arrow_at C _ _ x hx, ← fare_pair _ q (p+p') hx,map_add,fare_pair,fare_pair, ofReal_add]; ring)
lemma arrow_scale (q : Flavor 0) (p : Flavor k) (t : ℝ) : arrow C q (t • p)=(t:ℂ) • arrow C q p :=
  Reads.uniq (arrow_at C _ _) (fun x (hx : x≠0) ↦ by
    rw [map_smul,arrow_at C _ _ x hx, ←fare_pair _ q (t • p) hx,map_smul,fare_pair]; simp; ring)

def shoot (k : ℕ) (x : Space) (r : Flavor 0) : Echo k where
  toFun p := aeval x (arrow C r p)
  map_add' p q := by rw [arrow_add,map_add]
  map_smul' t p := by rw [arrow_scale,map_smul]; exact IsScalarTower.algebraMap_smul ℂ t (aeval x (arrow C r p))
lemma shoot_add (k : ℕ) (x : Space) (r s : Flavor 0) : shoot C k x (r+s)=shoot C k x r+shoot C k x s := by
  ext1 p; change aeval x _ = _ + _; rw [arrow_add_begin,map_add]; rfl

def dualCash (k : ℕ) : Module.Basis (Fin (Module.finrank ℝ (Flavor k))) ℝ (Flavor k) := Module.finBasis ℝ _
def changeNote (i : Fin (Module.finrank ℝ (Flavor k))) : Echo k :=
  Complex.ofRealCLM.toLinearMap.comp ((LinearMap.proj i).comp (dualCash k).equivFun.toLinearMap)
lemma faith (f : Echo k) : f= ∑ i, f (dualCash k i) • changeNote i := by
  apply LinearMap.ext; intro x
  conv_lhs => rw [← (dualCash k).sum_equivFun x]
  rw [map_sum,LinearMap.sum_apply]; refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul]; change _ = f (dualCash k i) • (↑((dualCash k).equivFun x i):ℂ); rw [Complex.real_smul,smul_eq_mul,mul_comm]

lemma tender (L : Echo k →ₗ[ℂ] ℂ) : ∃ p q : Flavor k, ∀ D : Echo k, L D = D p + I * D q := by
  let a i := L (changeNote (k:=k) i)
  refine ⟨∑ i, (a i).re • dualCash k i, ∑ i, (a i).im • dualCash k i, fun D ↦ ?_⟩
  conv_lhs => rw [faith D]
  rw [map_sum,map_sum,map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul,map_smul,map_smul]; change _ • a i = _
  simp only [Complex.real_smul, smul_eq_mul]
  conv_lhs => arg 2; rw [← re_add_im (a i)]
  ring

def doublet (r : Flavor 0) (p q : Flavor k) := arrow C r p + MvPolynomial.C I * arrow C r q
lemma doublet_scales (r : Flavor 0) (p q : Flavor k) : hyper (doublet C r p q) (k+2) := by
  intro x t; unfold doublet
  simp only [map_mul,map_add,aeval_C,Algebra.algebraMap_self,RingHom.id_apply]
  rw [arrow_scaling C _ _, arrow_scaling C _ _]; ring

lemma reversing (r : Flavor 0) (p : Flavor k) {x : E4} (hx : x ≠ 0) : fare C p r x = fare C r p (-x) := by
  exact exchange _ _ hx
lemma prices_ok (p q : Flavor k) (h : ∀ r, Obstructs (doublet C r p q)) : p=0 ∧ q=0 := by
  have hh (r : Flavor 0) : ∀ (x : E4), x ≠ 0 → (fare C r p x:ℂ) + I * (fare C r q x:ℂ)=0 := by
    obtain ⟨w,hw⟩ := chart_divides (h r)
    let f := fun x : E4 ↦ (fare C r p x:ℂ) + I * (fare C r q x:ℂ)
    have he : Pole (k+2+2) f := (poleFare C r p).add ((poleFare C r q).coord (I • ContinuousLinearMap.id ℝ ℂ))
    refine fun x hx ↦ clears_faint he (by omega) ?_ (x:=x) hx
    refine ⟨fun x ↦ aeval (paint x) w, polyReal w, fun x hx ↦ ?_⟩
    have H : aeval (paint x) (doublet C r p q) = sq (paint x)^(k+2+1)*f x := by
      simp only [doublet,map_add,map_mul,aeval_C,Algebra.algebraMap_self,RingHom.id_apply,f]; rw [arrow_at C _ _ x hx,arrow_at C _ _ x hx]; ring
    rw [hw,map_mul,chart_at,pow_succ'] at H
    dsimp only
    rw [show aeval (paint x) w = sq (paint x)^(k+2)*f x from mul_left_cancel₀ (paint_separate hx) (H.trans (mul_assoc ..))]
    rw [paint_sq, ← Complex.ofReal_pow, Complex.real_smul]; congr 2
  have ht (r : Flavor 0) (z : E4) (hz : z≠0) : fare C p r z=0 ∧ fare C q r z=0 := by
    rw [reversing _ _ _ hz,reversing _ _ _ hz]; have he := Complex.ext_iff.mp (hh r _ (neg_ne_zero.mpr hz)); simpa using he
  exact ⟨payment _ (fun z hz r ↦ (ht r z hz).1),payment _ (fun z hz r ↦ (ht r z hz).2)⟩

lemma seed (C : G.ColorIndex) : ∃ r : Flavor 0, ¬Obstructs (arrow C r (cell 0 1)) := by
  by_contra! h
  apply cell_alive
  apply (prices_ok C _ 0 ?_).1
  intro r x hx
  unfold doublet; rw [map_add,map_mul,h r x hx,show aeval x (arrow C r 0)=0 from map_zero (shoot C 0 x r)]; ring

def Links (x : Fin n → Space) (a y : Fin n) (k : ℕ) := {f : Echo k| ∃ (d : Space) (r : Flavor 0), Blip x a y d ∧ shoot C 0 (d-(x y-x a)) r≠0 ∧ f=shoot C k d r}
lemma resolve {x : Fin n → Space} (h : Dispersed x) {a y} (ha : a≠y) (L : Echo k →ₗ[ℂ] ℂ)
    (hp : ∀ f∈ Links C x a y k,L f=0) : L=0 := by
  obtain ⟨p,q,ht⟩ := tender L
  obtain ⟨w,hw⟩ := seed C
  obtain ⟨rfl,rfl⟩ : p=0 ∧ q=0 := prices_ok C p q (fun r ↦ by
    refine cone_extend h ha (arrow_scaling C w _) (doublet_scales C r p q) hw ?_
    intro d hd hv
    suffices hs : L (shoot C k d r)=0 by
      unfold doublet; simp only [map_add,map_mul,aeval_C,Algebra.algebraMap_self,RingHom.id_apply]; rw [ht] at hs; exact hs
    let b := d-(x y-x a)
    have he : shoot C 0 b w ≠ 0 := fun h ↦ hv (LinearMap.congr_fun h (cell 0 1))
    by_cases hf : shoot C 0 b r=0
    · have hw := hp (shoot C k d w) ⟨d,w,hd,he,rfl⟩
      have hx := hp (shoot C k d (r+w)) ⟨d,r+w,hd,(by change shoot C 0 b (r+w) ≠ 0; rw [shoot_add,hf,zero_add]; exact he),rfl⟩
      rwa [shoot_add,map_add,hw,add_zero] at hx
    exact hp _ ⟨d,r,hd,hf,rfl⟩)
  exact LinearMap.ext fun d ↦ by rw [ht d,map_zero,mul_zero,add_zero]; rfl

lemma spreads {x : Fin n → Space} (h : Dispersed x) {a y} (ha : a≠y) (k : ℕ) : Submodule.span ℂ (Links C x a y k)=⊤ := by
  apply Subspace.dualAnnihilator_inj.mp
  rw [Submodule.dualAnnihilator_top]; apply le_antisymm _ bot_le
  intro L hL; apply (Submodule.mem_bot ..).mpr (resolve C h ha L (fun f hf ↦ (Submodule.mem_dualAnnihilator ..).mp hL _ (Submodule.subset_span hf)))

end YM.SchemeConversionRG11.Corona
