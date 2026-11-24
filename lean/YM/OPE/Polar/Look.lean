import YM.Space.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
/-!
# Finite sets of good normals

For every pair in a finite fixed cloud (of differences; sizes irrelevant even
when disparate log layers), a normal avoids separated-projection ties
simultaneously, AND can be chosen as close to any prescribed basis vector
as we like. Constant loss of tilt depending only on configuration arity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Polar
open Function Set Filter Metric Submodule
open scoped Topology BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius
variable {I:Type}[Fintype I] (x:I→E4)

lemma rotate_up {x:E4}(h:‖x‖=1): ∃ K:Ortho, Ortho.motion K x=basis timeAxis:= by
    let p:= basis timeAxis; let v:=(ℝ ∙ (x-p))ᗮ; let M:= v.reflection; let A:= EuclideanSpace.basisFun Axis ℝ; refine ⟨⟨_, M.toMatrix_mem_unitaryGroup A A⟩,?_⟩; let f:= (M.toLinearEquiv.toLinearMap)
    change Matrix.toEuclideanLin (LinearMap.toMatrix A.toBasis A.toBasis f) x=_; rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,Matrix.toLin_toMatrix]; exact reflection_sub (h.trans (basis_norm _).symm)
private lemma widen (s:Finset I) (h:∀ i, x i≠0):Dense {y:E4|∀ i∈s, inner ℝ y (x i) ≠0}:=by
    induction s using Finset.induction with
    | empty=> simp
    | insert i s he ih=>
       let G:={y:E4|inner ℝ y (x i)≠0}; have hg:IsOpen G:= isOpen_ne.preimage (show Continuous (fun y:E4=> inner ℝ y (x i)) from by fun_prop)
       have hh:Dense G:=by
          refine dense_iff_inter_open.mpr fun U ho hU=>?_ ; obtain ⟨u,hu⟩:=hU; by_cases hv: u∈ G; · exact ⟨u,hu,hv⟩
          let f (t:ℝ):= u+t • x i; have ht:Tendsto f (𝓝[>] (0:ℝ)) (𝓝 u):=by
             have he:f 0=u:= by simp [f]
             exact (he ▸ ((show Continuous f from by unfold f; fun_prop).continuousAt (x:=0)).tendsto).mono_left nhdsWithin_le_nhds
          obtain ⟨t,ht,hT⟩:= ((ht.eventually (ho.mem_nhds hu)).and (show ∀ᶠ t in 𝓝[>] (0:ℝ),0<t from self_mem_nhdsWithin)).exists
          refine ⟨f t,ht,?_⟩; change inner ℝ (u+t • x i) (x i) ≠ 0; rw [inner_add_left, real_inner_smul_left, (show inner ℝ u (x i)=0 from by contrapose! hv; exact hv), zero_add]; exact mul_ne_zero hT.ne' (real_inner_self_pos.mpr (h i)|>.ne')
       rw [show {y:E4|∀ j∈ insert i s,inner ℝ y (x j)≠0}= G ∩ {y | ∀ j∈s,inner ℝ y (x j)≠0} by ext; simp [G]]; exact hh.inter_of_isOpen_left ih hg

variable {x}
lemma focus (h:∀ i, x i≠0) (a:Axis)(ε:ℝ)(he:0<ε): ∃ v:E4, ‖v‖=1∧ ‖v-basis a‖<ε ∧ ∀ i, inner ℝ v (x i)≠0:= by
    let f(y:E4):=‖y‖⁻¹ • y; let u:=basis a; have hp:f u=u:=(by simp [f,u]); have hN : u≠0:= norm_pos_iff.mp (by unfold u; rw [basis_norm]; norm_num)
    have he' : ∀ᶠ y in 𝓝 u, y≠0 ∧ f y∈ball u ε:=by
       have hh:ContinuousAt f u:= by unfold f; fun_prop (disch := aesop)
       rw [ContinuousAt,hp] at hh; exact (eventually_ne_nhds hN).and (hh.eventually (ball_mem_nhds u he))
    obtain ⟨y, hy, h, hz⟩:= (widen x Finset.univ h).inter_nhds_nonempty he'
    have hf:= norm_pos_iff.mpr h
    refine ⟨f y,?_,?_,fun i=>?_⟩
    · unfold f; rw [norm_smul,Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hf.ne']
    · simpa only [mem_ball,dist_eq_norm] using hz
    unfold f; rw [real_inner_smul_left]; exact mul_ne_zero (inv_ne_zero hf.ne') (hy _ (Finset.mem_univ i))

abbrev EyeRay := {x:E4//‖x‖=1}
def forwards (K:Ortho):EyeRay:= ⟨(Ortho.motion K).symm (basis timeAxis), by rw [LinearIsometryEquiv.norm_map,basis_norm]⟩
lemma locates (K:Ortho)(x:E4) : time (Ortho.motion K x) = inner ℝ (forwards K).val x:= by
    unfold time; rw [← (Ortho.motion K).inner_map_map, ← basis_inner, show Ortho.motion K (forwards K|>.val) = _ from LinearIsometryEquiv.apply_symm_apply ..]

private abbrev View (I:Type) := I→ EyeRay
private instance : CompactSpace EyeRay:= isCompact_iff_compactSpace.mp (show IsCompact {x:E4| ‖x‖=1} from ( (by simpa [sphere] using (isCompact_sphere (0:E4) 1))))
lemma watches (a:Axis)(ε:ℝ)(hp:0<ε):∃ s: Finset (Ortho×ℝ), (∀ z∈s, 0 < z.2 ∧ ‖(forwards z.1).val - basis a‖<ε) ∧
    ∀ f:I→E4, (∀ i,f i ≠ 0) → ∃ z∈ s, ∀ i, z.2 * ‖f i‖ ≤ |time (Ortho.motion z.1 (f i))| := by
    let T:=View I; let V:={z:Ortho×ℝ// 0<z.2 ∧ ‖(forwards z.1).val-basis a‖<ε}; let F: V→Set T:= fun z=>{f|∀ i,z.val.2 < |inner ℝ (forwards z.val.1).val (f i).val|};
    have hO(z):IsOpen (F z):= by rw [show F z=⋂ i:I,{f:View I|z.val.2 < |inner ℝ (forwards z.val.1).val (f i).val|} by ext; simp [F,T]]; exact isOpen_iInter_of_finite fun i=> isOpen_lt continuous_const (by fun_prop)
    have hT y:y∈⋃ z,F z:=by
       obtain ⟨u,hu,hx,hP⟩:= focus (show ∀ i,(y i).val≠ (0:E4) from fun i=> norm_pos_iff.mp (by rw [(y i).property]; norm_num)) a ε hp
       obtain ⟨K,hK⟩:= rotate_up hu; have hh:(forwards K).val=u:= by unfold forwards; dsimp only; rw [← hK]; exact LinearIsometryEquiv.symm_apply_apply ..
       obtain ⟨r,hr,hF⟩:= ((show ∀ᶠ i in 𝓝[>] (0:ℝ), 0 < i from self_mem_nhdsWithin).and ((eventually_all (p:=fun (i:I) t=> t < |inner ℝ u (y i).val|)  ).mpr (fun i=> (gt_mem_nhds (abs_pos.mpr (hP i))).filter_mono nhdsWithin_le_nhds))).exists -- named p?
       refine mem_iUnion.mpr ⟨⟨(K,r),hr,hh.symm ▸ hx⟩,fun i=>?_⟩; change r< |inner ℝ (forwards K).val (y i).val|; rw [hh]; exact hF i
    obtain ⟨t,ht⟩:= (isCompact_univ (X:=View I)).elim_finite_subcover F hO (fun x _=>hT x)
    refine ⟨t.image Subtype.val,fun z hz=>by obtain ⟨x,h,rfl⟩:= Finset.mem_image.mp hz; exact x.property, ?_⟩ -- indentation
    intro f hf; have hx(i):0<‖f i‖:=norm_pos_iff.mpr (hf i); let v(i):EyeRay:= ⟨‖f i‖⁻¹ • f i,by rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr (hx i)).le,inv_mul_cancel₀ (hx i|>.ne')]⟩
    obtain ⟨u,hu,hV⟩:= mem_iUnion₂.mp (ht (Set.mem_univ v)); refine ⟨_,Finset.mem_image_of_mem _ hu,fun i=>?_⟩; let B:=u.val; let y:=(forwards B.1).val; have hp := hV i; change B.2 < |inner ℝ y (‖f i‖⁻¹ • f i)| at hp; rw [real_inner_smul_right, abs_mul, abs_of_pos (inv_pos.mpr (hx i)), mul_comm,← div_eq_mul_inv] at hp; rw [locates]; exact (le_div_iff₀ (hx i)).mp hp.le
end YM.OPE.Polar
