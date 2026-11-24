import YM.PertExtension.PositionNetwork

/-!
# Coherent all-order X-space frame solves when the finite-leading test is regular

This is an algebraic, not a regulator-limit assertion. The zeroth
frame and the inputs must come from explicit diagram prescriptions for
perturbative use. The permitted positive-degree variations form a real
matrix submodule (`D.Z`); in applications it includes maps preserving the
field flag and the reality and H conventions, killing the unit. Calibration
means the finite linear combinations after transforming ALL slots attain
their free values (not imposing the tests on an unrelated vacuum table).
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace YM.PertExtension.Position
open Set Function Filter PowerSeries
open scoped Topology ContDiff BigOperators Classical
variable {J P : Type*} [Fintype J]{arity : P→ℕ}

structure First (p : ℝ⟦X⟧)(f : ℝ→ℝ) : Prop where
  match_zero : constantCoeff p=f 0
  condition : HasDerivAt f (coeff 1 p) 0

namespace First
variable {p q : ℝ⟦X⟧}{f g : ℝ→ℝ}
theorem mul (hf : First p f)(hg : First q g) : First (p*q) (f*g) := by
  constructor
  · simp [hf.match_zero,hg.match_zero]
  rw [coeff_one_mul,hf.match_zero,hg.match_zero,mul_comm ((coeff 1) q)]; exact hf.condition.mul hg.condition
theorem add (hf : First p f)(hg : First q g) : First (p+q) (f+g) := by
  constructor
  · simp only [map_add,hf.match_zero,hg.match_zero,Pi.add_apply]
  rw [map_add]; exact hf.condition.add hg.condition
theorem const (x : ℝ) : First (C x) (fun _ => x) := by constructor; exact constantCoeff_C ..; rw [coeff_C, if_neg (by decide)]; exact hasDerivAt_const ..
theorem indet : First X (fun t=>t):= by constructor; exact constantCoeff_X; rw [coeff_one_X];exact hasDerivAt_id' _
theorem sum {I : Type*}(s : Finset I){p : I→ℝ⟦X⟧}{f : I→ℝ→ℝ}(h:∀ i∈s,First (p i) (f i)): First (∑ i∈s,p i) (fun t=> ∑ i∈s,f i t):= by
  constructor
  · exact (map_sum _ _ _).trans (Finset.sum_congr rfl fun i hi => (h i hi).match_zero)
  rw [map_sum]; exact HasDerivAt.fun_sum fun i hi => (h i hi).condition
theorem prod {I : Type*}(s : Finset I){p : I→ℝ⟦X⟧}{f : I→ℝ→ℝ}(h:∀ i∈s,First (p i) (f i)): First (∏ i∈s,p i) (fun t=>∏i∈s,f i t):=by
  induction s using Finset.induction_on with
  | empty=>simp;simpa using const 1
  | insert i s hi ih=>
    simp [hi]
    exact (h i (by simp)).mul (ih (fun j hj=>h j (by simp [hj])))
theorem eval {a:Mark J arity→ℝ⟦X⟧}{k : FrameAt J ℝ⟦X⟧}{a' : ℝ→Mark J arity→ℝ}{k':ℝ→FrameAt J ℝ}
    (h : ∀ v,First (a v) (fun t=>a' t v))(hk : ∀ i j,First (k i j) (fun t=>k' t i j))(v:Mark J arity):
    First (insert J arity a k v) fun x=>insert J arity (a' x) (k' x) v :=
  sum Finset.univ fun w _=>(h ⟨v.1,w⟩).mul (prod Finset.univ fun _ _=>hk _ _)
end First

private lemma readings (a : Mark J arity→ℝ)(k u : FrameAt J ℝ)(v:Mark J arity) : HasDerivAt
    (fun t:ℝ => insert J arity a (k+t • u) v)
    (coeff 1 (insert J arity (PowerSeries.C ∘ a) (fun i j=>PowerSeries.C (k i j)+PowerSeries.C (u i j) * X) v)) 0 := by
   apply First.condition; apply First.eval (a':=fun (_:ℝ)=>a) (k':=fun z=> k+z•u) (fun v=>First.const (a v)) _
   intro i j
   simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
   convert (First.const (k i j)).add ((First.const (u i j)).mul First.indet) using 2
   simp only [Pi.add_apply,Pi.mul_apply]
   ring

def Questionnaire (s : Finset P) := (p : {i//i∈s}) × (Fin (arity p.1)→J)
private lemma finite_test (s : Finset P) : Finite (Questionnaire (J:=J) (arity:=arity) s):= inferInstanceAs (Finite ((p:s) × (Fin (arity p.val)→J)))
attribute [local instance] finite_test
-- canonical fintype on the sigma when opened
instance (s : Finset P) : Fintype (Questionnaire (J:=J) (arity:=arity) s):= Sigma.instFintype

def markIn (s:Finset P) : Questionnaire (J:=J) (arity:=arity) s → Mark J arity := fun ⟨p,v⟩=>⟨p.val,v⟩

/-- Finite real square diagnostics on frame variations, with extra scalar
entries for checks or higher calibrations permitted in `arity`. Choosing them
from free rank is a separate problem. -/
structure TestSystem (J P : Type*) [Fintype J](shape : P→ℕ) where
  Z : Submodule ℝ (FrameAt J ℝ)
  tests : Finset P
  select : (Questionnaire (J:=J) (arity:=shape) tests→ℝ) →ₗ[ℝ] Z
  baseline : FrameAt J ℝ
  target : Z

namespace TestSystem
variable (D : TestSystem J P arity)

def result (a : Questionnaire (J:=J) (arity:=arity) D.tests→ℝ)(k : FrameAt J ℝ) :=
  D.select (insert J (fun i:D.tests=>arity i.val) a k)

def lieResult (a) (z:D.Z):= D.result a (D.baseline+z.val)
def inspect (a : Mark J arity→ℝ) : D.Z →ₗ[ℝ] D.Z :=
  (fderiv ℝ (D.lieResult (a ∘ markIn D.tests)) 0).toLinearMap

lemma result_eq (a : Mark J arity→ℝ)(k:FrameAt J ℝ) : D.result (a ∘ markIn D.tests) k = D.select (insert J arity a k ∘ markIn D.tests):=by
  unfold result
  rfl

lemma lieResult_contDiff (a) : ContDiff ℝ ω (D.lieResult a):=
  D.select.toContinuousLinearMap.contDiff.comp (by
    apply contDiff_pi.mpr
    intro v
    unfold insert; apply ContDiff.sum; intro w _; apply ContDiff.mul (g:=fun k:D.Z=>∏ i,(D.baseline + k.val) (v.2 i) (w i)) contDiff_const
    apply contDiff_prod; intro i hi
    exact (ContinuousLinearMap.proj _).contDiff.comp ((ContinuousLinearMap.proj _).contDiff.comp (ContDiff.add contDiff_const D.Z.subtypeL.contDiff)))

lemma lieDeriv (a : Mark J arity→ℝ)(z:D.Z) : D.inspect a z =
  D.select (fun v=>coeff 1 (insert J arity (PowerSeries.C ∘ a)
    (fun i j=>PowerSeries.C (D.baseline i j)+PowerSeries.C (z.val i j) * X) (markIn _ v))) := by
   have hs : HasDerivAt (fun t : ℝ=>D.lieResult (a ∘ markIn D.tests) (t • z)) (D.inspect a z) 0 := by
      have := (ContDiff.differentiable (D.lieResult_contDiff (a ∘ markIn _)) (by simp)) (x:=(0:ℝ) • z) |>.hasFDerivAt
      unfold inspect
      rw [← zero_smul ℝ z]
      exact this.comp_hasDerivAt 0 (show HasDerivAt (fun r:ℝ=>r • z) z 0 by
         simpa using! (hasDerivAt_id' (0:ℝ)).smul_const z)
   refine hs.unique (D.select.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 ?_)
   apply hasDerivAt_pi.mpr; exact fun v=> readings _ _ _ (markIn D.tests v)

def response (a : Mark J arity→ℝ⟦X⟧)(k : FrameAt J ℝ⟦X⟧)(n : ℕ) :=
  D.select (fun v=>coeff n (insert J arity a k (markIn D.tests v)))

lemma response_bound (a : Mark J arity→ℝ⟦X⟧){n : ℕ}{k l : FrameAt J ℝ⟦X⟧}(z : D.Z) (hn:n>0)
    (hk : ∀ i j,Strike n (k i j) (l i j) (z.val i j)) (hC : ∀ i j, (k i j).constantCoeff=D.baseline i j) :
    D.response a k n + D.inspect (fun v=>constantCoeff (a v)) z = D.response a l n := by
  rw [D.lieDeriv]
  unfold response; rw [←map_add]; congr 1
  ext r
  simpa only [Pi.add_apply,hC, Function.comp_def] using! Strike.evaluation (v:=markIn (arity:=arity) (J:=J) D.tests r) (a:=a) hn hk |>.value

structure Regular (a₀ : Mark J arity→ℝ) : Prop where
  fits : D.result (a₀ ∘ markIn _) D.baseline=D.target
  rank : Function.Bijective (D.inspect a₀)

def repair (a : Mark J arity→ℝ⟦X⟧) :=
  if hy : Function.Bijective (D.inspect (fun v=>(a v).constantCoeff)) then (LinearEquiv.ofBijective _ hy).symm.toLinearMap else (0:Module.End ℝ D.Z)

def patch (a : Mark J arity→ℝ⟦X⟧)(n : ℕ)(previous : FrameAt J ℝ⟦X⟧) (i j : J) : ℝ⟦X⟧ :=
   let x := D.repair a (-(D.response a previous n))
   previous i j+C (x.val i j) * X^n

def stack (a : Mark J arity→ℝ⟦X⟧) (n : ℕ) : FrameAt J ℝ⟦X⟧ :=
  match n with
  | 0 => fun i j=>C (D.baseline i j)
  | .succ m => D.patch a (m+1) (stack a m)

lemma patch_scales (a : Mark J arity→ℝ⟦X⟧)(n : ℕ)(k : FrameAt J ℝ⟦X⟧):
  ∃ z:D.Z, D.patch a n k=(fun i j=>k i j+C (z.val i j)*X^n) ∧ ∀ i j,Strike n (k i j) (D.patch a n k i j) (z.val i j) := by
  exact ⟨_,rfl,fun i j=>⟨fun i hi=> by simp [patch, hi.ne], by simp [patch]⟩⟩

lemma stabilizes (a : Mark J arity→ℝ⟦X⟧)(m) : ∀ n ≤ m,∀ i j,coeff n (D.stack a n i j)=coeff n (D.stack a m i j):=by
  induction m with
  | zero=>simp
  | succ m ih=>
    intro n hn i j; obtain hn|rfl:=lt_or_eq_of_le hn; swap; rfl
    rw [ih _ (Nat.le_of_lt_succ hn),stack]
    exact (D.patch_scales a _ _).choose_spec.2 i j |>.lower _ hn

def position (a : Mark J arity→ℝ⟦X⟧) i j := PowerSeries.mk (fun n=> coeff n (D.stack a n i j))

@[simp] lemma position_zero (a : Mark J arity→ℝ⟦X⟧) i j : constantCoeff (D.position a i j)=D.baseline i j := by rw [← coeff_zero_eq_constantCoeff_apply]; simp [position,stack]

lemma positive_variation (a : Mark J arity→ℝ⟦X⟧)(n : ℕ)(hn : n≠0) :
    (fun i j=>coeff n (D.position a i j))∈D.Z := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  let K (f : FrameAt J ℝ⟦X⟧):= fun i j=>coeff n.succ (f i j)
  have he : (fun i j=>coeff n.succ (D.position a i j))=K (D.stack a n.succ) := by simp [position,K]
  rw [he,stack]; suffices d :K (D.patch a n.succ (D.stack a n))=0+D.repair a (-D.response a (D.stack a n) n.succ) from d ▸ (by simp)
  apply funext; intro i;funext j
  have h : K (D.stack a n) i j=0:= by
    suffices ∀ m≤n, K (D.stack a m) i j=0 from this _ le_rfl
    intro m h
    induction m with
    | zero=>simp [K,stack]
    | succ m ih=>rw [stack]; unfold K patch; rw [map_add,coeff_C_mul_X_pow,if_neg (by omega),add_zero];exact ih (by omega)
  simp [patch,K,h]

theorem normalizes {a : Mark J arity→ℝ⟦X⟧}(h : D.Regular (fun v=>(a v).constantCoeff)) (n):
  D.response a (D.position a) n= if n=0 then D.target else 0 := by
  by_cases hn:n=0
  · subst n; rw [if_pos rfl]; rw [← h.fits, D.result_eq]
    simp only [comp_def,response,coeff_zero_eq_constantCoeff_apply]
    simp only [insert_alg,D.position_zero]
  rw [if_neg hn]
  obtain ⟨j,rfl⟩:= Nat.exists_eq_succ_of_ne_zero hn
  have hh := D.patch_scales a j.succ (D.stack a j)
  obtain ⟨z,hz,hk⟩:=hh
  have ht (i j':J) : Strike j.succ (D.stack a j i j') (D.position a i j') (z.val i j') := by
    have he: ∀ n≤j.succ,coeff n (D.position a i j') = coeff n (D.stack a j.succ i j'):= fun n hn=> by simpa only [position,coeff_mk] using! D.stabilizes a _ n hn i j'
    exact ⟨fun n hn=> ((hk i j').lower _ hn).trans (he n hn.le |>.symm), ((hk i j').value).trans (he _ (le_refl _) |>.symm)⟩
  rw [← D.response_bound _ z (by omega) ht]
  · have hx : z=D.repair a (-D.response a (D.stack a j) j.succ) := by
      ext i j'
      have hm := congr_arg (fun p=>coeff j.succ (p i j')) hz
      simp only [patch,map_add,coeff_C_mul_X_pow] at hm
      exact (add_left_cancel hm).symm
    rw [hx,repair,dif_pos h.rank]
    let e:=LinearEquiv.ofBijective (D.inspect _) h.rank
    change _ + e (e.symm _) = 0
    rw [e.apply_symm_apply,add_neg_cancel]
  intro i j'
  simpa using (ht i j').lower _ (Nat.zero_lt_succ _)

theorem uniqueness {a : Mark J arity→ℝ⟦X⟧}(h : D.Regular (fun v=>(a v).constantCoeff)) {k l : FrameAt J ℝ⟦X⟧}
    (hk : ∀ n,D.response a k n=D.response a l n) (hk' : ∀ i j,constantCoeff (k i j)=D.baseline i j)
    (hl' : ∀ i j,constantCoeff (l i j)=D.baseline i j) (hz : ∀ n > 0,(fun i j=>coeff n (l i j)-coeff n (k i j))∈D.Z):
    k=l:=by
  suffices ∀ n,∀ i j,coeff n (k i j)=coeff n (l i j) by ext i j n; exact this ..
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih=>
    obtain rfl |hN := n.eq_zero_or_pos
    · intro i j; simpa only [coeff_zero_eq_constantCoeff_apply] using (hk' i j).trans (hl' i j).symm
    let z : D.Z := ⟨_,hz n hN⟩
    have He := D.response_bound a z hN (fun i j=>show Strike _ (k i j) (l i j) _ from ⟨fun s hs=>ih s hs i j,(by unfold z; simp)⟩) hk'
    have hi : D.inspect (fun v=>(a v).constantCoeff) z= D.inspect (fun v=>(a v).constantCoeff) 0 := by rw [map_zero]; simpa only [← hk,add_eq_left] using He
    have hh : z=(0:D.Z):=h.rank.injective hi
    exact fun i j=>(sub_eq_zero.mp (show coeff n (l i j)-coeff n (k i j)=0 from congr_arg (fun x:D.Z=>x.val i j) hh)).symm
end TestSystem
end YM.PertExtension.Position
