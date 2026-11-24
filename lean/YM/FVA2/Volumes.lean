import YM.FVA2.TreeBasis

/-!
# Link basis determinant helpers for FP proof

All relative determinants use linear coords at the zero background **before** gauge fixing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.TreeBasis.Volumes
open FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open PertExtension MS MS.Bare MS.Bare.Maurer LinearMap Function Finset
open scoped Classical Topology ContDiff
open Module
section
variable {X Y:Type} [AddCommGroup X][AddCommGroup Y][Module ℝ X][Module ℝ Y]

theorem insertion_det (e : X ≃ₗ[ℝ] Y) (A : X→ₗ[ℝ] Y) (B:Y→ₗ[ℝ] Y) :
    LinearMap.det (e.symm.toLinearMap ∘ₗ B ∘ₗ A) = LinearMap.det B * LinearMap.det (e.symm.toLinearMap ∘ₗ A) := by
   rw [← (det_conj B e.symm), ← det_comp]; congr 1; ext x; simp

variable [FiniteDimensional ℝ X][FiniteDimensional ℝ Y]

theorem lower_det (f:(X×Y)→ₗ[ℝ] (X×Y)) (a:X→ₗ[ℝ] X)(b:Y→ₗ[ℝ] Y)
    (h11:∀ x,(f (x,0)).1=a x) (h12:∀ y,(f (0,y)).1=0) (h22:∀ y,(f (0,y)).2=b y):
    LinearMap.det f= LinearMap.det a * LinearMap.det b:=by
    let v:=Module.finBasis ℝ X; let w:=Module.finBasis ℝ Y; let c:= LinearMap.snd ℝ X Y ∘ₗ (f.comp (LinearMap.inl ℝ X Y))
    have hv i: (v.prod w) (.inl i)=(v i,0) := Prod.ext (v.prod_apply_inl_fst w i) (v.prod_apply_inl_snd w i)
    have hw i: (v.prod w) (.inr i)=(0,w i) := Prod.ext (v.prod_apply_inr_fst w i) (v.prod_apply_inr_snd w i)
    rw [← det_toMatrix (v.prod w),show toMatrix (v.prod w) (v.prod w) f = Matrix.fromBlocks (toMatrix v v a) 0 (toMatrix v w c) (toMatrix w w b) from ?_,Matrix.det_fromBlocks_zero₁₂,det_toMatrix,det_toMatrix];
    ext (i|i) (j|j)
    all_goals first | rw [Matrix.fromBlocks_apply₁₁,toMatrix_apply,hv,v.prod_repr_inl w,h11,toMatrix_apply] | rw [Matrix.fromBlocks_apply₁₂,toMatrix_apply,hw,v.prod_repr_inl w,h12,map_zero]; rfl | (rw [Matrix.fromBlocks_apply₂₁,toMatrix_apply,hv,Basis.prod_repr_inr,toMatrix_apply]; rfl) | rw [Matrix.fromBlocks_apply₂₂,toMatrix_apply,hw,Basis.prod_repr_inr,h22,toMatrix_apply]

theorem upper_det (f:(X×Y)→ₗ[ℝ] (X×Y)) (a:X→ₗ[ℝ] X)(b:Y→ₗ[ℝ] Y)
    (h11:∀ x,(f (x,0)).1=a x) (h21:∀ x,(f (x,0)).2=0) (h22:∀ y,(f (0,y)).2=b y):
    LinearMap.det f= LinearMap.det a * LinearMap.det b:=by
   let e:=LinearEquiv.prodComm ℝ X Y
   rw [← det_conj f e]
   exact (lower_det _ b a h22 h21 h11)|>.trans (mul_comm ..)
end

variable {V E : Type} {G : Gauge} {D : Loom V E} {T : D.Truss}
variable [Fintype V][Fintype E]
variable (G T)
theorem pick_point (b : Free T G) (A : Links E G) : treeIso G T ((axes G T b).symm A).1=pick G T A := by
    obtain ⟨⟨p,c⟩,rfl⟩ := (axes G T b).surjective A
    rw [LinearEquiv.symm_apply_apply,charges,map_add,entry, add_zero]
    exact Eq.symm (funext (split_tree G T b p))
-- be careful determinant triangular direction

theorem tree_det (b : Free T G) :
     LinearMap.det ((axes G T b).symm.toLinearMap ∘ₗ (axes G T 0).toLinearMap) = 1 := by
   let e:=axes G T b; let F:= axes G T 0; let B:=e.symm.toLinearMap ∘ₗ F.toLinearMap
   have he : LinearMap.det B=LinearMap.det (LinearMap.id (R:=ℝ) (M:=Root D G))*LinearMap.det (LinearMap.id (R:=ℝ) (M:= Free T G)) := by
     have hx (y:Free T G) : B (0,y)=(0,y):=by
        change e.symm (F _) = _; apply e.injective
        rw [LinearEquiv.apply_symm_apply]; unfold F e; rw [charges,charges,map_zero,map_zero]
     apply lower_det
     · intro x; apply (treeIso G T).injective; change treeIso G T (e.symm (F _)).1=treeIso G T x; unfold F e; rw [pick_point, charges,map_zero, add_zero]; exact picks G T x
     exact fun u=> congr_arg Prod.fst (hx u)
     exact fun u=> congr_arg Prod.snd (hx u)
   exact he.trans (by rw [det_id,det_id,mul_one])

variable {G T} (Z : SectionBasis D T G)
theorem match_det : LinearMap.det ((axes G T 0).symm.toLinearMap ∘ₗ Z.equiv.toLinearMap)=1 := by
   let B:=(axes G T 0).symm.toLinearMap ∘ₗ Z.equiv.toLinearMap
   have hx (p) : B (p,0)=(p,0):=by
        apply (axes G T 0).injective; change axes G T 0 ((axes G T 0).symm (Z.equiv _))= _; rw [LinearEquiv.apply_symm_apply,Z.equiv_acts,charges,map_zero,map_zero]
   have he : LinearMap.det B=LinearMap.det (LinearMap.id (R:=ℝ) (M:=Root D G))*LinearMap.det (LinearMap.id (R:=ℝ) (M:= Free T G)) := by
      apply upper_det
      · exact fun p=> congr_arg Prod.fst (hx p)
      · exact fun p=> congr_arg Prod.snd (hx p)
      intro p; change whereL G T (Z.equiv _)=p; rw [Z.equiv_acts,map_zero,zero_add,Z.agreement]
   exact he.trans (by rw [det_id,det_id,mul_one])

theorem projected_det (b : Free T G) : LinearMap.det (Z.equiv.symm.toLinearMap ∘ₗ Z.full b)=Z.fpdet b := by
   let B:=Z.equiv.symm.toLinearMap ∘ₗ Z.full b
   have hx (v:Free T G) : Z.full b (0,v)=Z.L v := by unfold SectionBasis.full; simp
   have hv (v:Free T G): B (0,v)=(0,v):= by
      apply Z.equiv.injective; change Z.equiv (Z.equiv.symm _)=_; rw [LinearEquiv.apply_symm_apply,hx, Z.equiv_acts,map_zero,zero_add]
   rw [show Z.fpdet b=LinearMap.det (Z.ghosts b) * LinearMap.det (LinearMap.id (R:=ℝ) (M:=Free T G)) by rw [det_id,mul_one]; rfl]; change LinearMap.det B=_
   apply lower_det
   · intro x; have he : Z.full b (x,0)=directed G D (Z.L b) x:= by unfold SectionBasis.full; simp
     change (Z.equiv.symm (Z.full b (x,0))).1=_; rw [he]; rfl
   exact fun x=> congr_arg Prod.fst (hv x)
   exact fun x=> congr_arg Prod.snd (hv x)
-- regularity of determinant of operator from differentiating on inputs
section
variable {X Y : Type*}[NormedAddCommGroup X][NormedSpace ℝ X]
   [NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y]
theorem smooth_det {p : X} (f : X → Y →ₗ[ℝ] Y) (h : ∀ y,ContDiffAt ℝ ω (fun x=>f x y) p) :
    ContDiffAt ℝ ω (fun x=>LinearMap.det (f x)) p := by
   let B:= finBasis ℝ Y
   simp_rw [← det_toMatrix B (f _),Matrix.det_apply,toMatrix_apply]
   apply ContDiffAt.sum; intro σ _; refine ContDiffAt.const_smul _ (contDiffAt_prod (fun i _ => ?_)) -- order?
   exact (show ContDiffAt ℝ ω (fun x: X=> (B.coord (σ i)).toContinuousLinearMap (f x (B i))) p from (B.coord (σ i)).toContinuousLinearMap.contDiff.contDiffAt.comp p (h _))
end
end YM.FVA2.TreeBasis.Volumes
