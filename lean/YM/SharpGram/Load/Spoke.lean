import YM.SharpGram.Load.Tensor

/-!
# Euclidean load projections on equivariant components

Don't need orthogonality in any given norm on Quot. Use compact Haar average
on *full group*. All realized lifts also (same) linear. Aux quadratures not
assuming any diagonal. Intended for sharp output in a genuine load-bearing
stress sector.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Load
open Function Filter Set Table Climb Analysis Org Extraction Spec Next.UVStress MeasureTheory
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G: Gauge}{L:Register G}{S:Table L}{C:Family G}

section pr
attribute [local instance] OPE.Orbits.measO OPE.Orbits.borelO YM.Work.A15.compact_ortho
local instance : SecondCountableTopology Ortho := by
    haveI:SecondCountableTopology M4:= inferInstanceAs (SecondCountableTopology (Axis→Axis→ℝ))
    exact inferInstanceAs (SecondCountableTopology ↥(Matrix.unitaryGroup Axis ℝ : Set M4))
local notation "μ" => OPE.Orbits.haar
local instance : OPE.Orbits.haar.IsHaarMeasure := by unfold OPE.Orbits.haar; infer_instance
local instance : IsProbabilityMeasure μ := by unfold OPE.Orbits.haar; exact ⟨Measure.haarMeasure_self⟩
local instance {G:Gauge}{L:Register G}(S:Table L)(d:ℕ): FiniteDimensional ℝ (S.Field d) := Module.Finite.trans ℂ _
variable (R:S.Rotation){V: DiffPlan S}{H:S.RealSpin}
variable (hR:R.Laws V H){d:ℕ}
def Intervenes (w:S.Field d →ₗ[ℂ] S.Field d) : Prop := ∀ g x, w (R.act d g x) = R.act d g (w x)

def tow (w:Spin.Mat (S.Field d))(g:Ortho) : Spin.Mat (S.Field d):= renders d R g * w * renders d R g⁻¹
def spoke (w:Spin.Mat (S.Field d)):= ∫ g,tow R w g ∂μ
variable {R}
lemma tow_value (w:Spin.Mat (S.Field d))(g:Ortho) (x:S.Field d): tow R w g x= R.act d g (w (R.act d g⁻¹ x)):=rfl
include hR
private lemma speaking (w:Spin.Mat (S.Field d)) : Integrable (tow R w) μ:= by
   exact (((renders_live d hR).mul_const w).mul ((renders_live d hR).comp continuous_inv)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma takesCare (w:Spin.Mat (S.Field d)): Intervenes R (spoke R w).toLinearMap:= by
   let X := Spin.Mat (S.Field d)
   have hu: Integrable (tow R w) μ:= speaking hR _
   have hv(g:Ortho): spoke R w * renders d R g=renders d R g * spoke R w:=by
     let P : X→L[ℝ] X := ((ContinuousLinearMap.mul ℂ X).flip (renders d R g)).restrictScalars ℝ
     let Q : X→L[ℝ] X := (ContinuousLinearMap.mul ℂ X (renders d R g)).restrictScalars ℝ
     change P (∫ v,tow R w v ∂μ)=Q (∫ v,tow R w v ∂μ)
     rw [← P.integral_comp_comm hu,← Q.integral_comp_comm hu, ← (measurePreserving_mul_left μ g).integral_comp (g:=fun v=> P (tow R w v)) (Homeomorph.mulLeft g).measurableEmbedding]; apply integral_congr_ae; filter_upwards with v
     change renders d R (g*v)*w*renders d R (g*v)⁻¹ * renders d R g = renders d R g* (renders d R v*w*renders d R v⁻¹)
     rw [mul_assoc,←renders_sends d hR,show (g*v)⁻¹*g=v⁻¹ from by group, renders_sends d hR]; simp only [mul_assoc]
   exact fun g x=> DFunLike.congr_fun (hv g) x
/-- Lift on the exact image on *equivariant* managers. Will be used in
completely reducing one isotypic truss. -/
lemma descent (w:Module.End ℂ (S.Field d))(hw:Intervenes R w) : ∃ A:Module.End ℂ (S.Field d), Intervenes R A ∧ ∀ x∈LinearMap.range w,w (A x)=x:= by
    let U:= LinearMap.range w; let E:= S.Field d
    obtain ⟨J,hJ⟩:= LinearMap.exists_rightInverse_of_surjective (LinearMap.rangeRestrict w) (LinearMap.range_rangeRestrict w)
    obtain ⟨b,hb⟩:= LinearMap.exists_leftInverse_of_injective U.subtype (Submodule.ker_subtype _)
    let C := LinearMap.toContinuousLinearMap (J.comp b)
    have hx (g:Ortho)(x) (h:x∈U): R.act d g x∈U := by obtain ⟨v,rfl⟩:= h; exact ⟨_,hw g v⟩
    have hC (x) (h:x∈U): w (C x)=x := by
       let y:U := ⟨x,h⟩; have hz := LinearMap.congr_fun hb y
       change w (J (b (U.subtype y)))=y.val
       rw [show b (U.subtype y)=y from hz]
       exact congr_arg (fun z:U=>z.val) (LinearMap.congr_fun hJ y)
    refine ⟨(spoke R C).toLinearMap,takesCare hR _,fun x hx' =>?_⟩
    let Q := ((LinearMap.toContinuousLinearMap w).comp (ContinuousLinearMap.apply ℂ E x)).restrictScalars ℝ
    change Q (∫ v,tow R C v ∂μ)= x
    rw [← Q.integral_comp_comm (speaking hR C)]; simp_rw [show ∀ g:Ortho,Q (tow R C g)=x from (fun g=>by
       change w (R.act d g (C (R.act d g⁻¹ x)))=_; rw [hw,hC _ (hx _ _ hx'),← hR.group,mul_inv_cancel,hR.fixes]) ]
    simp

variable (U:Submodule ℂ (S.Field d))
structure Retraction (V:Submodule ℂ (S.Field d))(R:S.Rotation)(w:Module.End ℂ (S.Field d)) : Prop where
    inter_ : Intervenes R w
    slides : ∀ x,w x∈V
    fixes : ∀ x∈V,w x=x
lemma can_project (hv:∀ v (g:Ortho), v∈U → R.act d g v∈U) : ∃ p : Module.End ℂ (S.Field d), Retraction U R p := by
    obtain ⟨b,hb⟩:= LinearMap.exists_leftInverse_of_injective U.subtype (Submodule.ker_subtype _)
    let C:= LinearMap.toContinuousLinearMap (U.subtype.comp b)
    have hx (v) (h:v∈U): C v=v := congr_arg (fun z:U=>z.val) (LinearMap.congr_fun hb ⟨v,h⟩)
    refine ⟨(spoke R C).toLinearMap,takesCare hR _,fun x=> ?_,fun x h=> ?_⟩
    · let X:=Spin.Mat (S.Field d); let Q:= (ContinuousLinearMap.apply ℂ (S.Field d) x).restrictScalars ℝ
      let L' : X →L[ℝ] S.Field d:= C.restrictScalars ℝ |>.comp Q
      have hL (g:Ortho) : L' (tow R C g)=Q (tow R C g):= hx (tow R C g x) (hv _ g ((b _).property))
      have hP : L' (spoke R C)=Q (spoke R C) := by
           unfold spoke; rw [←L'.integral_comp_comm (speaking hR C),←Q.integral_comp_comm (speaking hR C)]; exact integral_congr_ae (Eventually.of_forall hL)
      change Q (spoke R C) ∈ _; rw [← hP]; exact (b _).property
    let Q := (ContinuousLinearMap.apply ℂ (S.Field d) x).restrictScalars ℝ
    change Q (∫ v,tow R C v ∂μ)=x; rw [← Q.integral_comp_comm (speaking hR C)]
    have he(g:Ortho): Q (tow R C g)=x:=by
       change R.act d g (C (R.act d g⁻¹ x))=_; rw [hx _ (hv _ _ h),← hR.group,mul_inv_cancel,hR.fixes]
    simp_rw [he]; simp

lemma Retraction.central {p:Module.End ℂ (S.Field d)}(h:Retraction U R p)
    (ht:∀ w:Module.End ℂ (S.Field d),Intervenes R w→∀ x∈U,w x∈U) {q:Module.End ℂ (S.Field d)} (hq:Intervenes R q):
    ∀ v,p (q v)=q (p v) := by
  let J:=p.comp (q.comp (LinearMap.id - p))
  have he(v):J v=p (q v)-p (q (p v)) := by simp [J]
  have hJ(v):J v∈U:= h.slides _
  have hV(v)(hv:v∈U): J v=0:= by rw [he,h.fixes v hv,sub_self]
  have hm : Intervenes R J := by intro g x; rw [he,he,h.inter_ g x,hq,hq,h.inter_,h.inter_,map_sub]
  obtain ⟨A,hA,ha⟩:= descent hR J hm
  intro v
  have hx : J v=0:=(ha _ ⟨v,rfl⟩).symm.trans (hV _ (ht A hA _ (hJ v)))
  rw [he,h.fixes _ (ht _ hq _ (h.slides v))] at hx; exact sub_eq_zero.mp hx
end pr
end YM.SharpGram.Load
