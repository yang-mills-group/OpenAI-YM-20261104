import YM.XSpace.Route

/-!
# Monochromatic costs in the cubic choice of gauge
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Chart2
open Module Lattice Function Set
open scoped Topology BigOperators InnerProductSpace
variable {G:Gauge} {R:Period} (T:R.Tree) (c : G.ColorIndex) {ι: Type*}

def axis := basisC G c
def mag : End ℝ G.Color := LinearMap.smulRight (innerₗ G.Color (basisC G c)) (basisC G c)
lemma mag_at (x:G.Color): mag c x=x c • basisC G c:=by change inner ℝ (basisC G c) x • basisC G c=x c • basisC G c; rw [EuclideanSpace.basisFun_inner]
lemma mag_sym (x y:G.Color): inner ℝ (mag c x) y=inner ℝ x (mag c y):=by rw [mag_at,mag_at,real_inner_smul_left,real_inner_smul_right,EuclideanSpace.basisFun_inner, real_inner_comm (basisC G c) x, EuclideanSpace.basisFun_inner,mul_comm]
lemma mag_axis (d : G.ColorIndex): mag c (basisC G d)= if d=c then basisC G d else 0:=by
  unfold mag; simp only [LinearMap.smulRight_apply]; change inner ℝ (basisC G c) _ • _=_
  rw [orthonormal_iff_ite.mp (basisC G).orthonormal]; split_ifs with h hh hh
  · simp [h]
  · exact False.elim (hh h.symm)
  · exact False.elim (h hh.symm)
  simp
lemma mag_component (x:G.Color) (d:G.ColorIndex): (mag c x) d= if d=c then x d else 0:=by
  rw [mag_at]; simp only [EuclideanSpace.basisFun_apply,PiLp.smul_apply,smul_eq_mul,PiLp.single_apply]
  split_ifs with h; simp [h]; simp

def light : End ℝ (ι→G.Color):=LinearMap.pi fun i=> mag c ∘ₗ LinearMap.proj i
lemma light_at (x:ι→G.Color) (i): light c x i=mag c (x i):=rfl
lemma light_polar (x:R.Bonds→G.Color): light c (polarized R x)=polarized R (light c x):=by
  unfold polarized; simp only [LinearMap.smul_apply,LinearMap.add_apply,LinearMap.id_coe,id_eq,map_add,map_smul]; congr 2; funext i; rw [R.mirror_apply,light_at,light_at,R.mirror_apply,map_neg]
lemma color_cover (A:T.Field G): light c (T.covering A)= T.covering (light c A):=by
  have h (i:R.Link): mag c (T.prolong A i)= T.prolong (light c A) i:= by unfold Period.Tree.prolong; split; rw [map_zero]; rfl
  funext i; simp only [light_at]; change mag c (if R.Chosen i then _ else _) = if R.Chosen i then _ else _; split_ifs; exact h _; exact (map_neg ..).trans (congr_arg Neg.neg (h _))

def rays (u:Carrier T G): Carrier T G:= (light c u.1,light c u.2)
def beam : End ℝ (Carrier T G) := (light c).prodMap (light c)
lemma beam_at (u:Carrier T G): beam T c u=(light c u.1,light c u.2):=rfl
lemma color_born (u:Carrier T G): light c (born T u)=born T (beam T c u):=by
  funext i; rw [light_at,born_at,born_at,beam_at]; by_cases H:R.vertex i=T.root; simp [H]
  rw [show rise T u.2 (R.vertex i)= _ from rise_at T u.2 ⟨_,H⟩]; exact Eq.symm (rise_at T (light c u.2) ⟨_,H⟩)
lemma color_dx (v:R.Sites→G.Color): light c (grad v)=grad (light c v):= by
  funext i; rw [light_at,grad_at,map_sub, grad_at,light_at,light_at]
lemma color_route (u:Carrier T G): light c (route T u)=route T (beam T c u):=by rw [routes,routes,map_add,color_cover,color_dx (R:=R),color_born]; rfl
lemma color_park (u:R.Bonds→G.Color): park T (light c u)=beam T c (park T u):=inject_route T (by rw [← color_route,undo_park,undo_park,light_polar])
lemma color_curl (u:LogLinks (Per R.side) G) (p : Face (Per R.side)): linearFace p (light c u)=mag c (linearFace p u):=by simp only [angular,light_at, map_sub,map_add]

lemma pi_light {ι: Type*} [Fintype ι] [DecidableEq ι] (j: Sigma fun _ : ι=> G.ColorIndex):
    let e:=Pi.basis (fun _ : ι => (basisC G).toBasis); light c (e j) = if j.2=c then e j else 0:=by
  dsimp only; rcases j with ⟨i,k⟩; rw [Pi.basis_apply]; funext x
  by_cases h:i=x; subst x; rw [light_at,Pi.single_eq_same,OrthonormalBasis.coe_toBasis,mag_axis]; split_ifs <;> simp
  rw [light_at,Pi.single_eq_of_ne (Ne.symm h),map_zero]; split_ifs <;> simp [Ne.symm h]
lemma in_dir (i:T.Key G) : light c (T.basis G i)=if i.2=c then T.basis G i else 0:= pi_light c i

def key : Knobs T G→ G.ColorIndex:= Sum.elim Sigma.snd Sigma.snd
lemma beam_axis (i : Knobs T G): beam T c (axisB T G i)= if key T i=c then axisB T G i else 0:=by
  rw [beam_at]; cases i with
  | inl i => rw [axisB_hor]; simp only [key,Sum.elim_inl,map_zero]; rw [in_dir]; split_ifs <;> rfl
  | inr i => rw [axisB_vert]; simp only [key,Sum.elim_inr,map_zero]; unfold nobasis; rw [pi_light]; split_ifs <;> rfl
lemma key_pixel (u:Carrier T G) (i:Knobs T G): (axisB T G).repr (beam T c u) i=if key T i=c then (axisB T G).repr u i else 0:=by
  classical
  conv_lhs=> rw [← (axisB T G).sum_repr u]; simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,beam_axis,smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · split_ifs <;> simp only [Basis.repr_self,Finsupp.single_eq_same,map_zero,Finsupp.zero_apply,mul_zero,mul_one]
  · intro j _ H; split_ifs <;> simp only [*, Finsupp.single_eq_of_ne (Ne.symm H),map_zero,Finsupp.zero_apply,mul_zero,Basis.repr_self]
  simp

lemma angle (i:T.Key G) (p: Face (Per R.side)) (c:G.ColorIndex): mag c (T.linearCurl (T.basis G i) p)=if i.2=c then T.linearCurl (T.basis G i) p else 0:=by
  let x:=T.basis G i
  unfold Period.Tree.linearCurl; rw [LinearMap.comp_apply,← curl_is R,← color_curl, color_cover,in_dir]; split_ifs <;> simp
lemma hess_pixel (G:Gauge) (i j:T.Key G) (h:i.2 ≠ j.2): T.hessian G i j=0:=by
  unfold Period.Tree.hessian; rw [LinearMap.BilinForm.toMatrix_apply,T.quadratic_val,Finset.sum_eq_zero,zero_div]
  intro p _; have hh:= mag_sym i.2 (T.linearCurl (T.basis G i) p) (T.linearCurl (T.basis G j) p); simpa [angle,Ne.symm h] using hh

lemma cov_chosen (G:Gauge) (i j:T.Key G) (h:i.2 ≠ j.2): T.covariance G i j=0:=by
  let F:= Matrix.diagonal (fun e:T.Key G=> if e.2=j.2 then (1:ℝ) else 0)
  have he : Commute F (T.hessian G) := by
    change F*_ =_ * F; ext m n; rw [Matrix.diagonal_mul, Matrix.mul_diagonal]; split_ifs with a b b <;> simp [*]
    · exact hess_pixel T G m n (by rwa [a, ne_comm])
    exact (hess_pixel T G m n (by rwa [b])).symm
  have ht : F*T.covariance G=T.covariance G*F := by
    apply (T.hessian_posDef G).isUnit.mul_right_inj.mp; rw [← mul_assoc,← he.eq,mul_assoc,← mul_assoc (T.hessian G), T.covariance_val,one_mul,mul_one]
  have hh := congr_fun (congr_fun ht i) j; rw [Matrix.diagonal_mul,Matrix.mul_diagonal] at hh; simpa [F,h] using hh.symm
end YM.XSpace.Chart2
