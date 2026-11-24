import YM.XSpace.ColorBeam
import YM.XSpace.JetGauge

/-!
# Construct `Setup` on the full odd Lie links to connect the first-order Ward computation
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Chart2
open Function Module JetGauge Lattice Finsupp MvPolynomial Next.Rank.Normal Drift
open scoped Topology BigOperators InnerProductSpace
variable {G:Gauge} {R:Period} (T:R.Tree)

def spaceCharge (G:Gauge) : LinearMap.BilinForm ℝ (Carrier T G):= (T.quadratic G).compl₁₂ (LinearMap.fst ℝ _ _) (LinearMap.fst ℝ _ _)
lemma charge (x y: Carrier T G):spaceCharge T G x y= T.quadratic G x.1 y.1:=rfl
lemma spacelike (x y:Carrier T G) :spaceCharge T G x y=(∑ p:Face (Per R.side),inner ℝ (linearFace p (route T x)) (linearFace p (route T y)))/2:= by rw [charge,T.quadratic_val]; simp_rw [route_face]

def guiding (G:Gauge):Setup (Knobs T G) G.ColorIndex where
  main:= Finset.univ.disjSum ∅
  grade:= key T
  k := ⟨(fun i j=> ↑(spaceCharge T G (axisB T G i) (axisB T G j))),fun i j=> congr_arg (fun t:ℝ=> (t:ℂ)) (show spaceCharge T G (axisB T G i) (axisB T G j)=_ from T.symmetric ..)⟩
  radical := by rintro (i|i) h j <;> simp only [Finset.mem_disjSum,Finset.mem_univ,Finset.notMem_empty] at h; simp at h
                dsimp only; rw [charge,axisB_vert]; simp
  mono := by
    rintro (i|i) (j|j) h <;> simp only [charge,axisB_vert,axisB_hor]
    · rw [← LinearMap.BilinForm.toMatrix_apply]; change ((T.hessian G i j:ℝ):ℂ)=0; rw [hess_pixel T G i j h]; simp
    all_goals simp
@[simp] lemma in_main (i:T.Key G) : Sum.inl i∈(guiding T G).main:=Finset.inl_mem_disjSum.mpr (Finset.mem_univ _)
@[simp] lemma outside (i): Sum.inr i∉(guiding T G).main:=by simp [guiding]
lemma under (i:Knobs T G) (h:i∉(guiding T G).main):route T (axisB T G i)= grad (born T (axisB T G i)):=by cases i <;> simp only [routes]; simp at h; rw [axisB_vert,map_zero,zero_add]

lemma reflected_r (a:R.Bonds→G.Color) (h: Legit R a) (u: Carrier T G): Legit R (rLink (born T u) a):=by
  ext1 i; rw [R.mirror_apply,r_at,r_at,legit_reflect h i, born_at, born_at, born_at,born_at, R.reflect_axis,R.reflect_dest,R.reflect_base,R.vertex_neg,R.vertex_neg, add_comm _ (rise T u.2 (R.vertex (i.1+step i.2)))]; simp
-- head i v-direction generator

def later (i:Knobs T G): End ℝ (Carrier T G):= park T ∘ₗ rLink (born T (axisB T G i)) ∘ₗ route T
lemma route_r (p:Knobs T G) (x:Carrier T G): route T (later T p x)=rLink (born T (axisB T G p)) (route T x):=by unfold later; rw [LinearMap.comp_apply,LinearMap.comp_apply,undo_park, polar_keeps _ (reflected_r T _ (legit_route T _) _)]
lemma beam_route (i:Knobs T G): light (key T i) (route T (axisB T G i))=route T (axisB T G i):=by rw [color_route,beam_axis,if_pos rfl]
lemma beam_born (i:Knobs T G): light (key T i) (born T (axisB T G i))=born T (axisB T G i):=by rw [color_born,beam_axis,if_pos rfl]
-- pitch orthogonality of rLink along the born flow
lemma mag_ad (u v : G.Color) (i:G.ColorIndex) (h: mag i u=u): mag i (G.ad u v)=0:=by
  rw [← h, mag_at i u] -- actually order
  simp only [_root_.map_smul,LinearMap.smul_apply]
  have he:=ad_e (basisC G i) v
  rw [mag,LinearMap.smulRight_apply,ad_swap (basisC G i)]; change u i • (inner ℝ (basisC G i) (-G.ad v (basisC G i)) • basisC G i)=_
  rw [inner_neg_right,he,neg_zero,zero_smul,smul_zero]
lemma mag_same (u v :G.Color) (i:G.ColorIndex) (h: mag i u=u) (hh:mag i v=v): G.ad u v=0:=by rw [← h,← hh]; simp [mag_at,ad_same]
lemma r_beam (c:G.ColorIndex) (u:R.Sites→G.Color) (A:R.Bonds→G.Color) (h: light c A=A): light c (rLink u A)=0:=by
  funext i; rw [light_at, r_at]; exact mag_ad _ _ c (congr_fun h i)
lemma mag_end {R:Period} (c:G.ColorIndex) (u:R.Sites→G.Color) (h: light c u=u) (i:R.Bonds): mag c ((1/2:ℝ) • (u (i.1+step i.2)+u i.1))= (1/2:ℝ) • (u (i.1+step i.2)+u i.1):=by rw [map_smul,map_add, show mag c (u _)=u _ from congr_fun h (i.1+step i.2), show mag c (u _)=u _ from congr_fun h i.1]
lemma beam_r (c:G.ColorIndex) (u:R.Sites→G.Color) (A:R.Bonds→G.Color) (h: light c u=u): light c (rLink u A)=0:=by
  funext i; rw [light_at,r_at,ad_swap (A i),map_neg,mag_ad _ _ c (mag_end (R:=R) ..),neg_zero]; rfl; exact h -- implicit h
lemma fixed_r (c:G.ColorIndex) (u:R.Sites→G.Color) (A:R.Bonds→G.Color) (h1:light c A=A) (h:light c u=u): rLink u A=0:=by
  funext i; rw [r_at]; apply mag_same _ _ c (congr_fun h1 i) (mag_end (R:=R) c u h i)
def leanB (G:Gauge) : (guiding T G).Turn where
  b x i j:= ↑((axisB T G).repr (later T x (axisB T G j)) i)
  mono x i j h:=by
    change key T i= key T j at h
    have hp:= key_pixel T (key T j) (later T x (axisB T G j)) i; rw [if_pos h] at hp
    have he : beam T (key T j) (later T x (axisB T G j))=0:=by apply inject_route T; rw [← color_route,route_r,r_beam (R:=R) _ _ _ (beam_route T j),map_zero]
    rw [← hp,he,map_zero]; simp
  born x i j h:=by
    change key T x=key T j at h
    have he : later T x (axisB T G j)=0:= by apply inject_route T; rw [route_r, fixed_r (R:=R) (key T x) _ _ (h.symm ▸ beam_route T j) (beam_born T x),map_zero]
    rw [he,map_zero]; simp
  exit x i j h:=by
    change key T x=key T i at h
    have hp:= key_pixel T (key T x) (later T x (axisB T G j)) i; rw [if_pos h.symm] at hp
    have he : beam T (key T x) (later T x (axisB T G j))=0:=by apply inject_route T; rw [← color_route,route_r,beam_r (R:=R) _ _ _ (beam_born T x),map_zero]
    rw [← hp,he,map_zero]; simp
end YM.XSpace.Chart2
