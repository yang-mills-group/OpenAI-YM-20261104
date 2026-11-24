import YM.XSpace.TopFourier
import YM.XSpace.Hessian

/-!
# Full-period curled Gaussian Hilbert space

We will also use transformations on this space when computing the reduced (inversion) covariance
and when fixing the Ward-compatible top subtractions. Scalars are always physical real colors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Top
open Function Filter Set Lattice Exterior Wilson Precision Matrix
open scoped Topology BigOperators InnerProductSpace
variable (G : Gauge) (n : Side)

abbrev Faces := Face (Per n)
abbrev Forms := PiLp 2 fun _ : Faces n => G.Color
abbrev Input := Exterior.fieldDir G n 1

def curl : Input G n →ₗ[ℝ] Forms G n where
  toFun u:= WithLp.toLp 2 fun i => Work.F03.faceCurl i u
  map_add' v w := by
    ext p i; change (((Exterior.d _ _) *ᵥ parts G 1 (v+w) i) _) = Work.F03.faceCurl p v i + Work.F03.faceCurl p w i
    rw [show parts G 1 (v+w) i=parts G 1 v i+parts G 1 w i from rfl,mulVec_add]; rfl
  map_smul' v w := by
    ext p i; change (((Exterior.d _ _) *ᵥ parts G 1 (v • w) i) _)= v • Work.F03.faceCurl p w i
    rw [show parts G 1 (v • w) i=v • parts G 1 w i from rfl,mulVec_smul]; rfl

lemma curl_val (u : Input G n) (p : Faces n) : curl G n u p=Work.F03.faceCurl p u:=rfl

abbrev Curled := LinearMap.range (curl G n)

-- reindex and act by the fundamental projector. Count every plaquette once.
def faces : Faces n ≃ Body 2 n:=Equiv.prodCongr (Equiv.refl _) plaqEquiv
def component (x : Forms G n) (i : G.ColorIndex) : form 2 n:= fun p=> x ((faces n).symm p) i
@[simp] lemma component_val (x : Forms G n) (i : G.ColorIndex) (p : Faces n) : component G n x i (faces n p)=x p i:=by rw [component,Equiv.symm_apply_apply]
lemma component_curl (x : Input G n) (i : G.ColorIndex) : component G n (curl G n x) i=Exterior.d 1 n *ᵥ parts G 1 x i:= by
  funext p; obtain ⟨p,rfl⟩:= (faces n).surjective p; rw [component_val]; rfl
lemma inner_forms (x y : Forms G n): inner ℝ x y=∑ i : G.ColorIndex, dotProduct (component G n x i) (component G n y i) :=by
  rw [PiLp.inner_apply]; simp_rw [PiLp.inner_apply,RCLike.inner_apply']
  rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
  unfold dotProduct; rw [← Equiv.sum_comp (faces n)]; simp

variable {G n} in
def project (x : Forms G n) : Forms G n:= WithLp.toLp 2 fun p => WithLp.toLp 2 fun i =>
    (projector n *ᵥ component G n x i) (faces n p)
lemma component_project (x : Forms G n) (i : G.ColorIndex) : component G n (project x) i=projector n *ᵥ component G n x i:=by
  ext1 p; obtain ⟨p,rfl⟩:= (faces n).surjective p; rw [component_val]; rfl
lemma same_iff (x y : Forms G n) (h : ∀ i, component G n x i=component G n y i) : x=y:= by
  ext p i; exact ((component_val _ _ _ _ _).symm.trans (congr_fun (h i) (faces n p))).trans (component_val ..)
lemma range_project (x : Forms G n) : project x ∈ Curled G n:=by
  obtain ⟨X,hX⟩:= (projection n).2.1
  let f : Input G n:= fun p => WithLp.toLp 2 fun i=> (X *ᵥ component G n x i) p
  refine ⟨f,same_iff G n _ _ fun i=>?_⟩
  rw [component_curl,component_project,hX,← mulVec_mulVec]; rfl
lemma proj_curls (x : Forms G n) (h : x∈Curled G n): project x=x:=by
  obtain ⟨u,rfl⟩:=h
  apply same_iff G n; intro i; rw [component_project,component_curl,mulVec_mulVec,(projection n).2.2]
lemma proj_symm (x y : Forms G n) : inner ℝ (project x) y=inner ℝ x (project y) := by
  rw [inner_forms,inner_forms]; apply Finset.sum_congr rfl; intro i _
  rw [component_project,component_project,dotProduct_mulVec,← mulVec_transpose, (projection n).1]
theorem full (x : Forms G n) : (Curled G n).starProjection x= project x:=by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (range_project G n x); intro w hw; rw [inner_sub_left,proj_symm,proj_curls G n _ hw,sub_self]

-- single-face sources in position formulas
variable {G n}
def unitFace (p : Faces n) (i : G.ColorIndex): Forms G n:= WithLp.toLp 2 <| Pi.single p (EuclideanSpace.basisFun G.ColorIndex ℝ i)
lemma atFace (x : Forms G n) (p : Faces n) (i : G.ColorIndex): inner ℝ (unitFace p i) x=x p i:=by
  rw [PiLp.inner_apply]; change ∑ t : Faces n, inner ℝ (Pi.single (M:=fun _=> G.Color) p (EuclideanSpace.basisFun G.ColorIndex ℝ i) t : G.Color) (x t)=_; rw [Finset.sum_eq_single p]
  · simp [EuclideanSpace.inner_single_left]
  · intro q _ h; rw [Pi.single_eq_of_ne h,inner_zero_left]
  simp
lemma atFace' (x : Forms G n) (p : Faces n) (i : G.ColorIndex): inner ℝ x (unitFace p i)=x p i:=by rw [real_inner_comm,atFace]
@[simp] lemma face_unit (p : Faces n) (i : G.ColorIndex) (q : Faces n) (j : G.ColorIndex) : unitFace p i q j= if p=q ∧ i=j then 1 else 0:= by
  change (Pi.single (M:=fun _=>G.Color) p (EuclideanSpace.basisFun G.ColorIndex ℝ i) q : G.Color) j=_; split_ifs with h
  · obtain ⟨rfl,rfl⟩:=h; simp
  by_cases he:p=q
  · rw [he,Pi.single_eq_same]; simp [*,EuclideanSpace.basisFun_apply]; tauto
  rw [Pi.single_eq_of_ne (Ne.symm he)]; rfl
lemma projects_unit (p q : Faces n) (i j : G.ColorIndex) : (Curled G n).starProjection (unitFace q j) p i=
    if i=j then projector n (faces n p) (faces n q) else 0 :=by
  rw [full,← component_val,component_project]; unfold mulVec dotProduct
  rw [← Equiv.sum_comp (faces n)]; simp_rw [component_val,face_unit]
  by_cases h:i=j
  · simp [*,mul_ite]
  simp [*,Ne.symm h]
lemma spectral (p q : Faces n) (i j : G.ColorIndex) {x : Cover} (h : wrap n x=p.1-q.1) :
    ↑(inner ℝ (unitFace p i) ((Curled G n).starProjection (unitFace q j)))=
      if i=j then fourier n p.2 q.2 x else (0:ℂ) :=by
  rw [atFace,projects_unit]; split_ifs; exact fourier_entry n _ _ _ _ h; simp
end YM.XSpace.Top
