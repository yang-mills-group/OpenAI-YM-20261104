import YM.Integration.WilsonMeasuredPublicEntranceMarkedQuadratics
import YM.Next.MAXWELL.House

/-! The finite matrices in the weight-four certificate are measured by the original
Maxwell curl propagator at distinct real collinear sites, with its actual distance and
colour normalization. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceQuadraticKernel
open Maxwell Maxwell.Free Tensor Analysis XSpace.Normalize
open WilsonMeasuredPublicEntranceQuadraticGrid WilsonMeasuredPublicEntranceQuadraticSpan
open WilsonMeasuredPublicEntranceMarkedQuadratics
open scoped Classical BigOperators
variable {G:Gauge}

def ray (a b:Axis):E4:=WithLp.toLp 2 fun i=>if i=a ∨ i=b then 1 else 0
theorem component (a b i:Axis):ray a b i=if i=a ∨ i=b then 1 else 0:=rfl
theorem nonzero(a b:Axis):ray a b≠0:=by
  intro h
  have eq:=congrArg (fun z:E4=>z a) h
  simp [component] at eq

theorem length (a b:Axis):‖ray a b‖^2=if a=b then 1 else 2:=by
  rw [EuclideanSpace.real_norm_sq_eq]
  by_cases eq:a=b
  · subst b
    simp [component,ite_pow]
  have value (i:Axis):(ray a b i)^2=(if i=a then 1 else 0)+(if i=b then 1 else 0):=by
    by_cases h:i=a <;> by_cases k:i=b <;> simp_all [component]
  norm_num [value,Finset.sum_add_distrib,eq]

theorem matrix (a b i j:Axis):houseM (ray a b) i j=(reflection a b i j:ℝ):=by
  simp only [houseM,Matrix.of_apply,length,component,kr_eq,reflection]
  split_ifs <;> simp_all
  norm_num

theorem scaled (a b:Axis){t:ℝ}(ht:t≠0):houseM (t • ray a b)=houseM (ray a b):=by
  ext i j
  simp only [houseM,Matrix.of_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    mul_inv_rev,PiLp.smul_apply,smul_eq_mul]
  field_simp [ht,norm_ne_zero_iff.mpr (nonzero a b)]

theorem original (a b:Axis)(i j:Six)(c e:G.ColorIndex){x y:E4}{t:ℝ}
    (ht:t≠0)(site:x-y=t • ray a b):
    K (omegaLeg c (left i) (right i)) (omegaLeg e (left j) (right j)) x y=
      if c=e then 4*normal*(‖x-y‖^2)⁻¹^2*lift (exterior a b) i j else 0:=by
  have apart:x≠y:=by
    intro eq
    rw [eq,sub_self] at site
    exact (smul_ne_zero ht (nonzero a b)) site.symm
  rw [omega_K_eq _ _ _ _ _ _ apart,bare_formula _ _ _ _ (sub_ne_zero.mpr apart)]
  congr 2
  change wedge (houseM (x-y)) _ _ _ _=_
  rw [site,scaled a b ht]
  simp only [wedge,matrix,at_cell,exterior,native_axes,Int.cast_sub,Int.cast_mul]
end YM.Integration.WilsonMeasuredPublicEntranceQuadraticKernel

