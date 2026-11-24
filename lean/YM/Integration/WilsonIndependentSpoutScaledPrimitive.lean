import YM.Integration.WilsonIndependentSpoutOpeningPost
import YM.Integration.WilsonIndependentPublicReportBias

/-! Return the whole native spring, including all lower thermal feeds, in
the scale of the independently calibrated chart. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutScaledPrimitive
open WilsonCoeffUV WilsonCoeffUV.Blue RegulatorIR RegulatorIR.Geometry
open RegulatorIR.Prim RegulatorIR.Binding RegulatorIR.Diagram RegulatorIR.Profiles
open RegulatorIR.Laplace RegulatorIR.Clocks PertExtension PertExtension.Series.Radial
open PowerSeries Lattice RG FreeResolvent Metric Tree
open WilsonIndependentSpoutOrdinarySpring
open scoped Classical BigOperators Topology ContDiff

theorem homogeneous {U:Type}[Fintype U](A:Cost)(unit:constantCoeff A=1)
    (f:Lawn U→ℝ)(k e:ℕ):
    mix A (sprig f k) e=∑i∈Finset.range (e+1),coeff (e-i) ((A⁻¹)^k) • sprig f k i:=by
  funext r
  simp only [mix,Finset.sum_apply,Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hit:k+i=r
  · subst r
    rw [pow_add,←mul_assoc,show A^i*(A⁻¹)^k*(A⁻¹)^i=(A*A⁻¹)^i*(A⁻¹)^k by rw [mul_pow];ring,
      PowerSeries.mul_inv_cancel _ (by rw [unit];norm_num),one_pow,one_mul]
  · rw [sprig,shine_dark hit,smul_zero,smul_zero]

private theorem read {U:Type}[Fintype U](A:Cost)(unit:constantCoeff A=1)
    (f:Lawn U→ℝ)(smooth:ContDiffAt ℝ ∞ f 0)(v:Lawn U)(k e:ℕ):
    MvPolynomial.eval v (totalR (mix A (sprig f k) e))=
    ∑i∈Finset.range (e+1),coeff (e-i) ((A⁻¹)^k)*coeff (k+i) (tale (fun t:ℝ=>f (t • v))):=by
  have fin (i:ℕ):FiniteGen (sprig f k i):=finite_shell (sprig_count f k) i
  rw [homogeneous A unit,visible_sum (fun i _=>finite_μ (fin i) _),map_sum]
  refine Finset.sum_congr rfl fun i _=>?_
  rw [visible_μ (fin i),Algebra.smul_def,map_mul,MvPolynomial.algebraMap_eq,MvPolynomial.eval_C,
    sprig,visible_shine,←Blue.jet_apply,rayon,lore smooth v,inscription,coeff_mk]
  rfl

private theorem shift (X B:Writing)(k e:ℕ)(under:∀i,i<k→coeff i X=0):
    (∑i∈Finset.range (e+1),coeff (e-i) B*coeff (k+i) X)=coeff (e+k) (B*X):=by
  rw [mul_comm B X,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j=>coeff i X*coeff j B)]
  rw [show (e+k).succ=k+(e+1) by omega]
  conv_rhs => rw [Finset.sum_range_add]
  have first:(∑i∈Finset.range k,coeff i X*coeff (e+k-i) B)=0:=by
    exact Finset.sum_eq_zero fun i hi=>by rw [under i (Finset.mem_range.mp hi),zero_mul]
  rw [first,zero_add]
  refine Finset.sum_congr rfl fun i _=>?_
  rw [show e+k-(k+i)=e-i by omega,mul_comm]

theorem scale (K:Feeds):tale K.scale.beta=(tale K.dine)⁻¹^2:=by
  let A:=tale K.dine
  have unit:constantCoeff A=1:=by
    rw [←coeff_zero_eq_constantCoeff_apply];exact tale_base.trans K.origin
  have inv:A*A⁻¹=1:=PowerSeries.mul_inv_cancel _ (by rw [unit];norm_num)
  calc tale K.scale.beta=tale K.scale.beta*(A^2*(A⁻¹)^2):=by rw [←mul_pow,inv,one_pow,mul_one]
       _=(tale K.dine)⁻¹^2:=by rw [←mul_assoc,show tale K.scale.beta*A^2=1 from
         WilsonIndependentPublicReportBias.square K,one_mul]

variable {G:Gauge}{c f:Side}(S:StepData c f)(F:Forest S.ratio)

theorem spring (branch:S.patch.Branches S.kernel G)(K:Feeds)
    {T:Branchix→Orders (KFoot G)}(V:Sphere S F K.scale T)
    (u:TreeVars G f)(b:TreeVars G c)(e:ℕ)(pos:0<e):
    (∑ p:Edge (Site c),drums (T (.inr (peg p)) e) (e+2) (joined u b))=
    -MvPolynomial.eval (tuple u b) (totalR (mix (tale K.dine) (sprig (jointPen G S) 2) e)):=by
  let v:=tuple u b
  let f:=fun t:ℝ=>jointPen G S (t • v)
  have smooth:ContDiffAt ℝ ∞ (jointPen G S) 0:=(penSmooth G S branch).of_le (by simp)
  have hf:ContDiffAt ℝ ∞ f 0:=by
    apply ContDiffAt.comp _ (g:=jointPen G S) (f:=fun t:ℝ=>t • v)
    · simpa using smooth
    exact (contDiff_id.smul contDiff_const).contDiffAt
  have nonneg (t:ℝ):0≤f t:=by
    unfold f jointPen Precision.noiseTaylor
    exact mul_nonneg S.kernel.penalty_pos.le (Finset.sum_nonneg fun _ _=>(G.price_range _).1)
  have hz:f 0=0:=by simp [f,(pen_jets G S branch).1]
  have under:=grows_sq hf nonneg hz
  have unit:constantCoeff (tale K.dine)=1:=by
    rw [←coeff_zero_eq_constantCoeff_apply];exact tale_base.trans K.origin
  rw [WilsonIndependentSpoutOrdinarySpring.original S F branch K.scale V u b e pos,
    read _ unit _ smooth]
  congr 1
  change coeff (e+2) (tale (K.scale.beta*f))=_
  rw [tale_mul K.scale.near hf,←scale K,shift (tale f) _ 2 e under]

end YM.Integration.WilsonIndependentSpoutScaledPrimitive
