import YM.WilsonCoeffUV.Series.Tensor
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Logic.Equiv.Fin.Rotate

/-! Literal germ readout into blue series in finite independent real
coordinates. Denominators X^a shifted *after* Taylor (residue hypotheses will
ensure no negative terms). Only ContDiffAt ω needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Function Filter PowerSeries
open scoped Topology ContDiff BigOperators Classical
variable {U V : Type*} [Fintype U] [Fintype V]
abbrev Lawn (U:Type*) := U→ℝ
abbrev Green {Y:Type*} [NormedAddCommGroup Y][NormedSpace ℝ Y](f:Lawn U→Y) := ContDiffAt ℝ ω f 0

section
variable {f g:Lawn U→ℝ}
def pebble (u:U) : Lawn U:= Pi.single u 1
lemma redeploy (u:Lawn U) : u=∑ i,u i • pebble i := by
  funext i; rw [Finset.sum_apply,Finset.sum_eq_single i] <;> simp +contextual [pebble]

def rub (f:Lawn U→ℝ)(i) := fun x=> fderiv ℝ f x (pebble i)
lemma rubbed (h :Green f) (i:U) : Green (rub f i) := ContDiffAt.comp (f:=fderiv ℝ f) 0 ((ContinuousLinearMap.apply ℝ ℝ (pebble i)).contDiff.contDiffAt) (h.fderiv_right (by simp))

def rye (f:Lawn U→ℝ) (k:ℕ) : Ten ℝ U k := fun x=> (k.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ k f 0 (pebble ∘ x)
lemma rye_sym {f:Lawn U→ℝ} (h:Green f)(k:ℕ) : Smooth (rye f k) := fun i x=> congrArg (fun a:ℝ=> (k.factorial:ℝ)⁻¹ • a) (h.iteratedFDeriv_comp_perm (pebble ∘ x) i)
lemma slice_rye (h:Green f)(k)(i) : (k+1) • prune (rye f (k+1)) i=rye (rub f i) k := by
  let L:=(ContinuousLinearMap.apply ℝ ℝ (pebble i))
  funext x; rw [Pi.smul_apply,prune]
  rw [← (rye_sym h (k+1)) (finRotate _) _, show Fin.cons i x ∘ _=Fin.snoc x i from (Fin.snoc_eq_cons_rotate x i).symm]
  have he : iteratedFDeriv ℝ (k+1) f 0 (pebble ∘ Fin.snoc x i) = iteratedFDeriv ℝ k (rub f i) 0 (pebble ∘ x) := by
    rw [iteratedFDeriv_succ_apply_right]
    simp only [Function.comp_apply, Fin.snoc_last]
    rw [show rub f i=(L ∘ fderiv ℝ f) from rfl,L.iteratedFDeriv_comp_left (h.fderiv_right (by exact le_top (a:=ω+1))) (by simp),show Fin.init _=pebble ∘ x from by funext; simp [Fin.init]]; rfl
  rw [rye,rye, he,nsmul_eq_mul]; simp [smul_eq_mul,Nat.factorial_succ]; field_simp

def jet (f:Lawn U→ℝ) : Ink U := PowerSeries.mk fun i=> paint i (rye f i)
@[simp] lemma jet_apply (f:Lawn U→ℝ)(i) : coeff i (jet f)=paint i (rye f i):= coeff_mk ..
lemma jet_lead (f:Lawn U→ℝ): constantCoeff (jet f)= MvPolynomial.C (f 0) := by rw [←coeff_zero_eq_constantCoeff_apply,jet_apply,shell _ (fun i=>i.elim0)]; simp [rye]

/-- Exact factorial ordinary evaluation on repeated m. -/
lemma rayon (f : Lawn U→ℝ)(i:ℕ)(m:Lawn U) : MvPolynomial.eval m (coeff i (jet f))=(i.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ i f 0 (fun _=>m) := by
  let L:= iteratedFDeriv ℝ i f 0
  rw [jet_apply,toll,show (fun _:Fin i=>m)=fun _=> ∑ j,m j • pebble j from funext fun _=>redeploy m]
  have h := L.toMultilinearMap.map_sum (fun (_:Fin i) j=> m j • pebble j)
  change L _ = ∑ x:Fin i→U,L (fun i=>m (x i) • pebble (x i)) at h
  change _= _ • L _; rw [h,Finset.smul_sum]; apply Finset.sum_congr rfl; intro x _
  rw [L.map_smul_univ]; change ((_:ℝ) • L _) * _ = _ • (_ • L _); simp only [smul_eq_mul,Function.comp_def]; ring
lemma sap (h: Green f)(i) : brush i (jet f)= X*jet (rub f i) := by
  ext1 k; cases k with
  | zero =>
    simp only [brush,blot_apply,jet_apply,shell (rye f 0) (fun i=>i.elim0),MvPolynomial.pderiv_C]; simp
  | succ k=> rw [brush,blot_apply,jet_apply, peel _ (rye_sym h _),← map_nsmul,slice_rye h]; simp
lemma jet_congr (h:f =ᶠ[𝓝 0] g) : jet f=jet g := by
  ext1 i; rw [jet_apply,jet_apply]; congr 1
  funext; unfold rye; rw [show iteratedFDeriv ℝ i f 0=iteratedFDeriv ℝ i g 0 from congr_fun ((h.ftaylorSeries (𝕜:=ℝ)).self_of_nhds (x:=0)) i]
lemma jet_add (h:Green f)(t:Green g) : jet (f+g)=jet f+jet g := by
  ext1 k; rw [map_add,jet_apply,jet_apply,jet_apply,←map_add]; congr 1; funext i; rw [Pi.add_apply, rye, rye, rye, iteratedFDeriv_add_apply (h.of_le (by simp)) (t.of_le (by simp)), add_apply,smul_add]
lemma jet_const (r:ℝ) : jet (fun _:Lawn U=>r)=realS r := by
  ext1 k; cases k with
  | zero=> rw [coeff_zero_eq_constantCoeff_apply,jet_lead]; simp
  | succ k=> rw [jet_apply,show rye _ _=0 from funext (fun i=> by simp [rye,iteratedFDeriv_const_of_ne])]; simp
lemma jet_sum {I:Type*}(s:Finset I)(F:I→ Lawn U→ℝ)(h:∀ i∈s,Green (F i)) : jet (∑ i∈s,F i)=∑ i∈s,jet (F i) := by
  induction s using Finset.induction_on with
  | empty=> simpa using! jet_const (U:=U) 0
  | @insert k s he ih =>
    rw [Finset.sum_insert he,Finset.sum_insert he,jet_add (h k (Finset.mem_insert_self ..)) (f:=F k) (g:=∑ j∈s,F j) (by
      unfold Green; simp_rw [← show (fun x=> ∑ j∈s,F j x)= ∑ j∈s,F j from funext fun x=> (Finset.sum_apply ..).symm]; exact ContDiffAt.sum (fun i hi=>h i (Finset.mem_insert_of_mem hi))), ih (fun i hi=>h i (Finset.mem_insert_of_mem hi))]

omit [Fintype U] in
lemma pext {p q:POL U} (h:MvPolynomial.eval (0:U→ℝ) p=MvPolynomial.eval 0 q)(he:∀ i,MvPolynomial.pderiv i p=MvPolynomial.pderiv i q) : p=q := by
  apply MvPolynomial.ext; intro n
  by_cases hh:n=0
  · subst n; simpa only [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq] using h
  obtain ⟨i,hv⟩ := Finsupp.ne_iff.mp hh
  change n i≠0 at hv
  have ha: n-Finsupp.single i 1+Finsupp.single i 1=n := Finsupp.sub_add_single_one_cancel hv
  have hy := congr_arg (MvPolynomial.coeff (n-Finsupp.single i 1)) (he i)
  rw [MvPolynomial.coeff_pderiv,MvPolynomial.coeff_pderiv,ha] at hy; exact mul_right_cancel₀ (by positivity) hy

def seedH : Ink U→+*PowerSeries ℝ := PowerSeries.map (MvPolynomial.eval (0:U→ℝ))
omit [Fintype U] in
lemma seed_eq {p q: Ink U}(h:seedH p=seedH q) (n) : MvPolynomial.eval (0:U→ℝ) (coeff n p)=MvPolynomial.eval 0 (coeff n q) := by
  simpa only [seedH,coeff_map] using congr_arg (coeff n) h
lemma seed_jet (f:Lawn U→ℝ): seedH (jet f)=C (f 0) := by
  ext n; unfold seedH; cases n with
  | zero => rw [coeff_map,coeff_zero_eq_constantCoeff_apply,jet_lead]; simp
  | succ n=> rw [coeff_map,jet_apply,scorch]; simp
lemma jet_mul (h:Green f)(t:Green g): jet (f*g)=jet f*jet g := by
  ext1 n; induction n using Nat.strong_induction_on generalizing f g with
  | h n ih =>
    apply pext (seed_eq (by simp only [seed_jet,map_mul]; simp) n)
    intro i
    have he : jet (rub (f*g) i)=jet (rub f i*g)+jet (f*rub g i) := by
      rw [←jet_add (f:=rub f i*g) (g:=f*rub g i) ((rubbed h i).mul t) (h.mul (rubbed t i))]; apply jet_congr
      filter_upwards [h.eventually (by simp),t.eventually (by simp)] with x hf hg
      unfold rub; simp only [Pi.mul_apply, Pi.add_apply]; rw [((hf.differentiableAt (by simp)).hasFDerivAt.mul ((hg.differentiableAt (by simp)).hasFDerivAt)).fderiv]; simp [mul_comm, add_comm]
    rw [show MvPolynomial.pderiv i (coeff n (jet (f*g)))= _ from (blot_apply _ _ _).symm];
    change coeff n (brush i (jet (f*g)))= _
    rw [←blot_apply, sap (f:=f*g) (h.mul t) i, he, show blot _ _=brush i (jet f*jet g) from rfl,Derivation.leibniz,sap h,sap t,smul_eq_mul,smul_eq_mul]
    conv_rhs => rw [mul_left_comm (jet f),mul_left_comm (jet g)]
    rw [← mul_add]; cases n with
    | zero=> simp
    | succ n=>
      simp only [coeff_succ_X_mul, map_add]
      rw [ih n (by omega) (rubbed h i) t, ih n (by omega) h (rubbed t i),mul_comm _ (jet g),add_comm]

lemma jet_neg (h:Green f) : jet (-f)= -jet f := by
  have hx : Green (-f):=h.neg
  have he:=jet_add hx h; rw [neg_add_cancel,show jet (0:Lawn U→ℝ)=0 from by simpa using! (jet_const (U:=U) 0)] at he
  exact eq_neg_of_add_eq_zero_left he.symm
lemma jet_sub (h: Green f)(t:Green g) : jet (f-g)=jet f-jet g := by rw [sub_eq_add_neg,jet_add h (show Green (-g) from t.neg), jet_neg t, sub_eq_add_neg]
lemma jet_arg (i : U) : jet (fun x:Lawn U=>x i)=X*path i := by
  let f (x:Lawn U):= x i
  apply PowerSeries.ext; intro n
  have hf : Green f:=(ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:U=>ℝ) i).contDiff.contDiffAt
  have he (j): rub f j= Function.const _ ((pebble j) i) := funext fun y=> by
    let L:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:U=>ℝ) i
    unfold rub; rw [show f=L from rfl,ContinuousLinearMap.fderiv]; rfl
  refine pext (seed_eq ?_ n) fun j=>?_
  · rw [seed_jet]; simp [seedH,path]
  have hv : brush j (jet f)=brush j (X*path i) := by
    rw [sap hf,he,show jet (Function.const (Lawn U) (pebble j i)) = _ from jet_const (pebble j i)]; rw [Derivation.leibniz,show brush j X=0 from blot_X _,brush_path]; by_cases h:i=j <;> simp [pebble, h]
  exact (blot_apply _ _ _).symm.trans ((congrArg (coeff n) hv).trans (blot_apply _ _ _))
end

-- y(F)=logs transform back RESCALED coordinates; variable X retained
section
variable (f:Lawn U→Lawn V)
def spool (i:V) : Ink U := mk fun n=> coeff (n+1) (jet (fun u=>f u i))
omit [Fintype V] in
@[simp] lemma spool_raised (h:f 0=0)(i:V) : X * spool f i=jet fun u=>f u i := by
  ext1 n; cases n with
  | zero => rw [coeff_zero_X_mul,coeff_zero_eq_constantCoeff_apply,jet_lead]; simp [h]
  | succ n=> simp only [coeff_succ_X_mul,spool,coeff_mk]
lemma spool_ext (i) (h:Green f)(e:f 0=0)(j) : brush j (spool f i) = jet (rub (fun u=>f u i) j) := by
  have he := sap (f:=fun u=>f u i) ((contDiffAt_apply ℝ ℝ ..).comp 0 h) j
  rw [← spool_raised f e i, Derivation.leibniz,show brush j X=0 from blot_X _] at he
  simp only [mul_zero,smul_eq_mul, add_zero] at he; exact mul_left_cancel₀ X_ne_zero he
omit [Fintype V] in
lemma underspool (i) : seedH (spool f i) = 0 := by
  ext n; simp only [seedH,coeff_map,spool,coeff_mk,jet_apply,paint,scorch,map_zero]
omit [Fintype V] in
lemma seed_train : (seedH.comp (train (spool f)))=seedH := by
  have hr r : seedH (realS (U:=V) r)= C r:=by simp [realS,seedH]
  apply serial_ext (by simp [seedH]) _ (by simp [seedH]); intro p
  induction p using MvPolynomial.induction_on with
  | C a=>
    rw [show C _ = realS _ from rfl,hr,RingHom.comp_apply,train_real]; exact (by simp [seedH,realS])
  | add p q a b=> simp_rw [map_add,a,b]
  | mul_X p i H=>
    simp only [map_mul,show C _=path i from rfl,H]
    rw [RingHom.comp_apply,train_path,underspool]; simp [path,seedH]

private lemma chainlaw (h:Green f)(e:f 0=0)(u:Lawn V→ℝ)(k:Green u)(i) : rub (u ∘ f) i =ᶠ[𝓝 0] ∑ j : V, rub (fun x=>f x j) i * (rub u j ∘ f) := by
  have H := h.continuousAt.tendsto; rw [e] at H
  filter_upwards [h.eventually (by simp),H.eventually (k.eventually (by simp))] with x a b
  rw [rub,fderiv_comp x (b.differentiableAt (by simp)) (a.differentiableAt (by simp)),ContinuousLinearMap.comp_apply,redeploy ((fderiv ℝ f x) (pebble i)), map_sum,Finset.sum_apply]
  let L (i:V):= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:V=>ℝ) i
  apply Finset.sum_congr rfl; intro j _; rw [map_smul,smul_eq_mul, Pi.mul_apply]; congr 1
  rw [rub,show (fun x=>f x j)=(L j ∘ f) from rfl, fderiv_comp x (L j).differentiableAt (a.differentiableAt (by simp)), ContinuousLinearMap.fderiv]; rfl

lemma traveling (h:Green f)(e:f 0=0)(u:Lawn V→ℝ)(k:Green u): train (spool f) (jet u) = jet (u ∘ f) := by
  apply PowerSeries.ext; intro n
  induction n using Nat.strong_induction_on generalizing u with
  | h n ih=>
    have hc (w : Lawn V→ℝ) (b:Green w) : Green (w ∘ f) := ContDiffAt.comp 0 (by rw [e]; exact b) h
    apply pext (seed_eq (by rw [←RingHom.comp_apply,seed_train,seed_jet u, seed_jet _]; simp [e]) n); intro i
    let F (j:V) := (rub (fun x=>f x j) i)
    let T (j:V) := (rub u j ∘ f)
    have ht j : Green (F j*T j):=(rubbed ((contDiffAt_apply ℝ ℝ ..).comp 0 h) i).mul (hc _ (rubbed k j))
    change _= MvPolynomial.pderiv i _
    rw [←blot_apply,←blot_apply];
    change coeff n (brush i _)=coeff n (brush i _)
    rw [sap (hc u k) i,jet_congr (chainlaw f h e u k i),jet_sum Finset.univ _ (fun i _=>ht i),reroutes]
    simp_rw [Finset.mul_sum,spool_ext f _ h e,fun j=>sap k j,map_mul,train_X,map_sum,mul_left_comm (jet (rub _ _)) X]
    apply Finset.sum_congr rfl; intro j _
    rw [jet_mul (f:=F j) (g:=T j) (rubbed ((contDiffAt_apply ℝ ℝ ..).comp 0 h) i) (hc _ (rubbed k _))]
    cases n with
    | zero=> rw [coeff_zero_X_mul,coeff_zero_X_mul]
    | succ n=>
      rw [coeff_succ_X_mul,coeff_succ_X_mul]
      exact ((Equal.refl (jet (F j)) _).mul (fun m hm=> ih m hm _ (rubbed k j))) n (n.lt_succ_self)
end
end YM.WilsonCoeffUV.Blue
