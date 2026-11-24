import YM.Integration.WilsonOrdinaryWardSpace

/-! Restricted finite measured equation in genuine real coordinates on
the allowed space of field corrections. No symmetry of the compact test
is used. -/
noncomputable section
namespace YM.Integration.WilsonOrdinaryAdmissibleEquation
open Filter Matrix Function LinearMap
open scoped Topology Matrix.Norms.Frobenius Classical
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (D : Submodule ℝ (Matrix I I ℂ))

def select : (Matrix I I ℂ) →ₗ[ℝ] D := D.subtype.leftInverse

omit [Fintype I] [DecidableEq I] in
theorem certify (u : D) : select D u.val=u := LinearMap.leftInverse_apply_of_inj D.ker_subtype u

def restricted (W : Matrix I I ℂ) : D →ₗ[ℝ] D :=
  (select D).comp ((LinearMap.mulRight ℝ W).comp D.subtype)

theorem read (W : Matrix I I ℂ) (x : D) : restricted D W x=select D (x.val*W) := rfl

noncomputable abbrev coordinates := Module.finBasis ℝ D
def table (W : Matrix I I ℂ) : Matrix (Fin (Module.finrank ℝ D)) (Fin (Module.finrank ℝ D)) ℝ :=
  LinearMap.toMatrix (coordinates D) (coordinates D) (restricted D W)

theorem pivot : table D 1=1 := by
  have id : restricted D 1=LinearMap.id := by
    apply LinearMap.ext;intro x;rw [read,mul_one,certify];rfl
  rw [table,id,LinearMap.toMatrix_id]

def correction (W P Z : Matrix I I ℂ) : D :=
  (coordinates D).equivFun.symm ((table D (W*Z))⁻¹ *ᵥ
    (coordinates D).equivFun (select D ((P-W)*Z)))

/-- The true measured D-equation is invertible before cutoffs and its
solution tends to zero on this actual field correction space. -/
theorem solved {X : Type*} {l : Filter X} {K : Matrix I I ℂ} (unit : IsUnit K)
    (W P : X→Matrix I I ℂ) (obs : Tendsto W l (𝓝 K)) (target : Tendsto P l (𝓝 K)) :
    Tendsto (fun i=>correction D (W i) (P i) K⁻¹) l (𝓝 0) ∧
    ∀ᶠ i in l,IsUnit (table D (W i*K⁻¹)) ∧
      select D (((1+(correction D (W i) (P i) K⁻¹).val)*W i-P i)*K⁻¹)=0 := by
  let Z := K⁻¹
  let T := fun i=>table D (W i*Z)
  let f := fun i=>select D ((P i-W i)*Z)
  let e := coordinates D
  have old : K*Z=1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp unit)
  have wlim : Tendsto (fun i=>W i*Z) l (𝓝 1) := old ▸ obs.mul tendsto_const_nhds
  have small : Tendsto T l (𝓝 1) := by
    rw [←pivot D]
    apply tendsto_pi_nhds.mpr;intro i
    apply tendsto_pi_nhds.mpr;intro j
    have stored := (select D).continuous_of_finiteDimensional.continuousAt.tendsto.comp
      ((tendsto_const_nhds (x:=(e j).val)).mul wlim)
    simp only [T,table,LinearMap.toMatrix_apply,read]
    simpa only [Function.comp_def,e,Module.Basis.coord_apply] using (e.coord i).continuous_of_finiteDimensional.continuousAt.tendsto.comp stored
  have delta : Tendsto (fun i=>(P i-W i)*Z) l (𝓝 0) := by
    simpa only [sub_self,zero_mul] using (target.sub obs).mul (tendsto_const_nhds (x:=Z))
  have forcing : Tendsto f l (𝓝 0) := by
    simpa only [f,map_zero,Function.comp_def] using (select D).continuous_of_finiteDimensional.continuousAt.tendsto.comp delta
  let Y := Fin (Module.finrank ℝ D)
  have inverse : Tendsto (fun i=>(T i)⁻¹) l (𝓝 1) := by
    have invC : ContinuousAt Inv.inv (1 : Matrix Y Y ℝ) :=
      continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv'];exact continuousAt_inv₀ (by simp))
    simpa only [inv_one,Function.comp_def] using invC.tendsto.comp small
  have joint : Continuous (fun p : Matrix Y Y ℝ × (Y→ℝ)=>p.1 *ᵥ p.2) := by
    apply continuous_pi;intro a
    change Continuous (fun p : Matrix Y Y ℝ × (Y→ℝ)=>∑ b,p.1 a b * p.2 b)
    apply continuous_finsetSum;intro b _
    fun_prop
  have charges : Tendsto (fun i=>e.equivFun (f i)) l (𝓝 0) := by
    simpa only [map_zero,Function.comp_def,LinearEquiv.coe_coe] using e.equivFun.continuous_of_finiteDimensional.continuousAt.tendsto.comp forcing
  have combined := joint.continuousAt.tendsto.comp (inverse.prodMk_nhds charges)
  have done := e.equivFun.symm.continuous_of_finiteDimensional.continuousAt.tendsto.comp combined
  constructor
  · simpa only [correction,e,T,f,Z,Function.comp_def,Matrix.one_mulVec,map_zero,LinearEquiv.coe_coe] using done
  have dets := ((continuous_id.matrix_det).continuousAt (x:=(1:Matrix Y Y ℝ))).tendsto.comp small
  have yes : (1:Matrix Y Y ℝ).det≠0 := by simp
  filter_upwards [dets.eventually_ne yes] with i stable
  have live : IsUnit (T i) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr stable)
  refine ⟨live,?_⟩
  let x := correction D (W i) (P i) Z
  have step : (T i) *ᵥ (e.equivFun x)=e.equivFun (f i) := by
    rw [show e.equivFun x= (T i)⁻¹ *ᵥ e.equivFun (f i) from e.equivFun.apply_symm_apply _,
      Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp live),Matrix.one_mulVec]
  have deliver : e.equivFun (restricted D (W i*Z) x)=(T i) *ᵥ (e.equivFun x) :=
    (LinearMap.toMatrix_mulVec_repr e e (restricted D (W i*Z)) x).symm
  have paid : select D (x.val*(W i*Z))=select D ((P i-W i)*Z) := e.equivFun.injective (deliver.trans step)
  change select D (((1+x.val)*W i-P i)*Z)=0
  rw [show (((1+x.val)*W i-P i)*Z)=x.val*(W i*Z)-(P i-W i)*Z by noncomm_ring,
    map_sub,paid,sub_self]

end YM.Integration.WilsonOrdinaryAdmissibleEquation
end
