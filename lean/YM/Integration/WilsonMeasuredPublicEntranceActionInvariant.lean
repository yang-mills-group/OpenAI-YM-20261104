import YM.TraceExtension.Foundation.Dilate

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace YM.Integration.WilsonMeasuredPublicEntranceActionInvariant
open Labels StressFlux Trace Maxwell Tensor
variable {G:Gauge}

theorem raw (simple:G.Simple) (v:Label G 4)
    (real:realBar v=v) (turn:∀ s:Signed,tensor s.ortho v=v) :
    ∃ u a:ℝ,v=u • unit G 4+a • square4 G:=by
  let D (i j:Axis) : Label G 4:=if i=j then v else 0
  have admitted:D ∈ RawTwo G:=by
    refine ⟨fun i j=>by simp [D,eq_comm],fun i j=>?_,fun s i j=>?_⟩
    · by_cases h:i=j <;> simp [D,h,conjR,real]
    · by_cases h:i=j
      · subst j
        simpa only [D,if_pos rfl,spinR,LinearMap.restrictScalars_apply,
          ←sq,sign_sq,one_smul] using turn s
      · simp [D,h,s.perm.injective.eq_iff]
  obtain ⟨t,src⟩:=labelStress_onto simple (⟨D,admitted⟩:RawTwo G)
  have diag (i:Axis):stress G t i i=v:=
    (congrArg (fun T:RawTwo G=>T.val i i) src).trans (if_pos rfl)
  have trace:=Finset.sum_congr (s₁:=Finset.univ) rfl (fun i _=>diag i)
  simp only [stress_of,if_true,Finset.sum_add_distrib,Finset.sum_const,
    ←Finset.smul_sum,Finset.card_univ,Fintype.card_fin] at trace
  refine ⟨t 0,t 1+4*t 2,?_⟩
  unfold square4
  linear_combination (norm := module) (-1/4:ℝ) • trace

theorem coordinates (simple:G.Simple) (F:Frame G 4) (y:F.Coeff)
    (real:∀ i,star (y i)=y i) (turn:∀ s:Signed,F.act s.ortho y=y) :
    ∃ u a:ℝ,y=u • F.e0+a • F.coords (square4 G):=by
  have bar:realBar (F.coords.symm y)=F.coords.symm y:=by
    apply F.coords.injective
    ext i
    rw [F.conj_basis,F.coords.apply_symm_apply,real]
  have spin (s:Signed) : tensor s.ortho (F.coords.symm y)=F.coords.symm y:=by
    apply F.coords.injective
    rw [←F.act_coords,F.coords.apply_symm_apply,turn]
  obtain ⟨u,a,h⟩:=raw simple _ bar spin
  use u,a
  simpa only [LinearEquiv.restrictScalars_apply,LinearEquiv.apply_symm_apply,
    map_add,F.coords_unit] using congrArg (F.coords.restrictScalars ℝ) h |>.trans
      (show (F.coords.restrictScalars ℝ) (u • unit G 4+a • square4 G)=_ from by
        rw [map_add,map_smul,map_smul]; change u • F.coords (unit G 4)+a • F.coords (square4 G)=_; rw [F.coords_unit])

end YM.Integration.WilsonMeasuredPublicEntranceActionInvariant
