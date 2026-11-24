import YM.AveragedStep.Orders.Rasps
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Filter Function Lattice RG Loops Tree Wilson Precision Metric Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
variable {c f:Side}{G:Gauge}{A:ChartRatio G}{P:Patch}{K:KernelChoices}{S:StepData c f}

abbrev Ink (G:Gauge) (c f:Side):= Rim c f × G.ColorIndex
def dashMark (x:G.Color)(i:G.ColorIndex):ℝ:=x i
def mon (w : List (Ink G c f))(Y:Hand G c f) :ℝ := (w.map (fun i=> dashMark (Y i.1) i.2)).prod
@[simp] lemma mon_nil (Y: Hand G c f): mon [] Y=1:=rfl
lemma mon_cons (a:Ink G c f)(w:List (Ink G c f))(Y):mon (a::w) Y = dashMark (Y a.1) a.2 * mon w Y:=rfl
abbrev fingers (G:Gauge)(i:G.ColorIndex):G.Color:=EuclideanSpace.basisFun G.ColorIndex ℝ i
lemma dash_eq (v : G.Color)(i:G.ColorIndex):dashMark v i = inner ℝ (fingers G i) v:=by
 rw [fingers,EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_left]; simp [dashMark]
def tickAt (i:Ink G c f):Hand G c f →L[ℝ] ℝ:=(innerSL ℝ (fingers _ i.2)).comp (ContinuousLinearMap.proj i.1)
lemma tick_def (i:Ink G c f)(Y):tickAt i Y=dashMark (Y i.1) i.2:= by rw [dash_eq];rfl
lemma tick_read (i j:Ink G c f): tickAt i (introAt j.1 (fingers G j.2)) = if i=j then 1 else 0:=by
 rcases i with ⟨i,e⟩; rcases j with ⟨j,k⟩; simp_rw [tick_def,intro_eq,dashMark,EuclideanSpace.basisFun_apply]
 by_cases h:i=j <;> by_cases he:e=k <;> simp [h,he]
lemma dash_bound (v:G.Color)(i:G.ColorIndex): |dashMark v i|≤‖v‖:= (dash_eq v i).symm ▸ (by
  simpa only [(EuclideanSpace.basisFun G.ColorIndex ℝ).orthonormal.1 i,one_mul] using abs_real_inner_le_norm (fingers G i) v)
lemma mon_cont (w:List (Ink G c f)):ContDiff ℝ 1 (mon w):=by
 induction w with
 | nil=> exact contDiff_const
 | cons a w ih=> rw [show mon (a::w)=(tickAt a:Hand G c f→ℝ)*mon w from funext (fun v=>by rw [mon_cons,Pi.mul_apply,tick_def])]; exact (tickAt a).contDiff.mul ih
-- Ordered rows. Derivatives as erasures retain repetitions (ONE contribution per slot)
def peel (i:Ink G c f) : List (Ink G c f) → Hand G c f → ℝ
 | [],_=>0
 | a::w,X=> (if a=i then mon w X else 0)+dashMark (X a.1) a.2*peel i w X
lemma peels (i:Ink G c f) (w:List (Ink G c f))(Y):fderiv ℝ (mon w) Y (introAt i.1 (fingers G i.2))=peel i w Y:=by
 induction w with
 | nil=> rw [show mon ([]: List (Ink G c f))=fun _=>1 from rfl,fderiv_const_apply]; rfl
 | cons a w ih=>
   have he := ((tickAt a).hasFDerivAt.mul ((mon_cont w).differentiable (by simp) Y|>.hasFDerivAt)).fderiv
   rw [show mon (a::w)= (tickAt a:Hand G c f→ℝ)*mon w from ?_,he,peel]
   swap; · exact funext fun v=>by rw [mon_cons,Pi.mul_apply,tick_def]
   simp only [add_apply,smul_apply,smul_eq_mul,ih]; rw [tick_read a i,tick_def]; split_ifs <;> ring
lemma peel_pay (i:Ink G c f)(w:List (Ink G c f))(Y){r:ℝ}(hr:1≤r)(hz:∀ p∈w,‖Y p.1‖≤r): |mon w Y|≤r^w.length ∧ |peel i w Y| ≤ w.length*r^w.length :=by
 induction w with
 | nil=> simp [mon_nil,peel]
 | cons p w ih=>
   obtain ⟨h1,h2⟩:=ih (fun p hp=> hz p (by simp [hp]))
   rw [List.length_cons,Nat.cast_add,Nat.cast_one,pow_succ,mul_comm _ r,mon_cons,abs_mul,peel]
   have ht := (dash_bound (Y p.1) p.2).trans (hz _ (by simp)); constructor
   · exact mul_le_mul ht h1 (abs_nonneg _) (by linarith)
   split_ifs
   swap; · rw [zero_add,abs_mul]; refine (mul_le_mul ht h2 (abs_nonneg _) (by linarith)).trans ?_; rw [add_mul,one_mul,mul_left_comm]; exact le_add_of_nonneg_right (by positivity)
   refine (abs_add_le ..).trans ((add_le_add h1 (d:= r*(w.length*r^w.length)) ?_).trans ?_)
   · exact (abs_mul _ _).le.trans (mul_le_mul ht h2 (abs_nonneg _) (by linarith))
   nlinarith [pow_nonneg (show 0≤r by linarith only [hr]) w.length,(le_mul_of_one_le_left (by positivity : 0 ≤ r^w.length) hr)]

-- cuff logarithms in real probability price (geometric cost in cup)
variable (F:Forest S.ratio)(C:Cuff S.patch S.kernel A)
def hands (x:Site c)(τ:ℝ)(p:TopologyQ F G):Hand G c f:= τ • grasp F C x p
lemma hands_cost {B:ℝ} (H:∀ u:G.El,‖C.logC u‖≤B*G.chord u)(hB:1≤B)(τ:ℝ)(ht:1≤τ)(b:Site c)(z:TopologyQ F G)(D:Finset (Rim c f))(i)(hi:i∈D): ‖hands F C b τ z i‖ ≤ B*cup F b τ D z:=by
 rw [hands,Pi.smul_apply,norm_smul_of_nonneg (by linarith)]
 calc
   _ ≤ τ*(B*G.chord (aboard F b z i)) := mul_le_mul_of_nonneg_left (H _) (by linarith)
   _ ≤ _:=by rw [mul_left_comm]; apply mul_le_mul_of_nonneg_left (cup_take F b τ (by linarith) hi z) (by linarith)
lemma hands_env (b:Site c)(τ:ℝ)(f':Hand G c f→ℝ)(h:Continuous f'): Envelope (fun z=> f' (hands F C b τ z)):=by
 let Z(z:TopologyQ F G):=hands F C b τ z
 have ht:Measurable Z := measurable_pi_lambda _ (fun i=>measurable_const.smul (C.log_meas.comp ((measurable_pi_apply i).comp (aboard_cont F b).measurable)))
 obtain ⟨B,H⟩:= isCompact_closedBall (0:Hand G c f) (‖τ‖*(2*C.width)) |>.exists_bound_of_continuousOn h.continuousOn
 refine ⟨h.measurable.comp ht,B,fun z=> H _ ?_⟩; rw [mem_closedBall_zero_iff,hands,norm_smul]; gcongr; exact (pi_norm_le_iff_of_nonneg (by have :=C.active; positivity)).mpr (fun i=>C.log_max _)
end YM.AveragedStep
