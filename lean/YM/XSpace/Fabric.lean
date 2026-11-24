import YM.XSpace.Compat.GaussTags
import YM.XSpace.Prism
import YM.XSpace.BallPay

/-!
# The Gram variables to feed at all the primary insertion points

Use a real matrix acting on the color of every TaylorTower used in the
polynomial evaluations. This action is defined without restricting to
isometries! After free Ward identities, orthogonal transformations (a priori
mixing singlets) can then be detected with additional weight-four probes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Sample
open Function Set Filter Maxwell Maxwell.Free MvPolynomial Next.Rank.Normal Legs
open scoped BigOperators Topology Classical RealInnerProductSpace ContDiff
variable {G : Gauge}
abbrev Motor (G:Gauge):= G.Color→L[ℝ] G.Color
abbrev Fabric (G:Gauge):= EuclideanSpace ℝ (G.ColorIndex×G.ColorIndex)

variable (M : Motor G)
def zoom (i : ℕ) (A : Shell G i): Motor G →ₗ[ℝ] Shell G i where
  toFun m:= faceMap i m A
  map_add' _ _:= rfl
  map_smul' _ _:=rfl

def motor (v:TaylorTower G): TaylorTower G:=fun i=> faceMap i M (v i)
lemma motor_one (v:TaylorTower G): motor 1 v=v:= rfl
lemma motor_mul (N : Motor G) (v:TaylorTower G): motor (M*N) v=motor M (motor N v):=rfl

-- extracting flavor commutes with this action
variable {j : ℕ}
def glean (A:Shell G j): Flavor j→ₗ[ℝ] G.Color where
  toFun := available A
  map_add' _ _:= rfl
  map_smul' _ _:= rfl
lemma shades (v:TaylorTower G) (p : Flavor j): available (motor M v j) p=M (available (v j) p):=by
  suffices h : glean (motor M v j) = M.toLinearMap ∘ₗ glean (v j) from DFunLike.congr_fun h p
  refine LinearMap.ext_on (unitStay j) ?_; rintro q ⟨u,i,m,rfl⟩; rfl
lemma fill_g (x:G.Color) (A:Sheet j) (p:Flavor j): available (fill j x A) p = p A • x := by ext1 i; change p (faceMap j (cp (G:=G) i) (fill j x A))= _; rw [which,map_smul,PiLp.smul_apply]; exact mul_comm ..
lemma travel_smooth (p:WickPol G) (T:TaylorTower G): ContDiff ℝ 1 (fun x : Motor G=> probe (motor x T) p):=by
  induction p using MvPolynomial.induction_on with
  | C a=> simpa only [probe,aeval_C,Algebra.algebraMap_self,RingHom.id_apply] using (contDiff_const (n:=1) (𝕜:=ℝ) (c:=a) (E:=Motor G))
  | add p q hp hq=>simp_rw [_root_.map_add]; exact hp.add hq
  | mul_X p i hp=>
    simp_rw [map_mul]; apply hp.mul; let f:= Complex.ofRealCLM ∘L ((coordinateLeg i).comp (zoom i.1 (T i.1))).toContinuousLinearMap
    convert! f.contDiff using 1; funext x; rw [probe,aeval_X]; rfl

section rows
variable {M}
def row (K:Fabric G) (i:G.ColorIndex): G.Color:=WithLp.toLp 2 fun j=> K (i,j)
def pump (K:Fabric G): Motor G:= LinearMap.toContinuousLinearMap 
    { toFun x:= WithLp.toLp 2 fun i=> ⟪x,row K i⟫
      map_add' a b:= by ext i; change ⟪a+b,_⟫=_+_; rw [inner_add_left]; rfl
      map_smul' t a:= by ext i; change ⟪t • a,_⟫=t*_; rw [real_inner_smul_left]; rfl }
lemma pumped (K:Fabric G) (x:G.Color) (i:G.ColorIndex): pump K x i=⟪x,row K i⟫:=rfl

def plank (M: Motor G) : Fabric G:= WithLp.toLp 2 fun i=> M (unitColor G i.2) i.1
@[simp] lemma able (M:Motor G): pump (plank M)=M:=by
  ext x i; change ⟪x,row _ i⟫= _; conv_lhs => rw [← color_sum x]; rw [sum_inner];
  conv_rhs=> rw [← color_sum x,map_sum,WithLp.ofLp_sum,Finset.sum_apply]
  simp_rw [real_inner_smul_left,_root_.map_smul,PiLp.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl; intro j _; rw [show ⟪unitColor G j,row (plank M) i⟫=(row (plank M) i) j from ?_]; rfl
  simp [unitColor,EuclideanSpace.inner_single_left]

def pillow (i:G.ColorIndex) (x : G.Color): Fabric G:= WithLp.toLp 2 fun j=> if j.1=i then x j.2 else 0
lemma relax (i:G.ColorIndex) (x:G.Color) (K:Fabric G): ⟪pillow i x,K⟫= ⟪x,row K i⟫:=by
  change (∑ j : G.ColorIndex×G.ColorIndex,(K j)*pillow i x j)= _
  rw [Fintype.sum_prod_type]; simp only [pillow,WithLp.ofLp_toLp,mul_ite,mul_zero]; simp_rw [Finset.sum_ite_irrel]; simp; rfl
lemma rests (i j:G.ColorIndex) (x y:G.Color): ⟪pillow j y,pillow i x⟫= if i=j then ⟪x,y⟫ else 0 := by
  rw [relax]; split_ifs with h; subst j; rw [show row (pillow i x) i=x by ext; simp [row,pillow]]; exact real_inner_comm _ _ -- direction?
  rw [show row (pillow i x) j=0 by ext; simp [row,pillow,Ne.symm h], inner_zero_right]
end rows
variable (A : E4→ TaylorTower G)
def bill (p : World G): Fabric G:= pillow p.2.2 (available (A p.1 p.2.1.1) p.2.1.2)

variable {n h : ℕ} {S : Finset E4} {L:Finset (World G)}
def carpet (h : ℕ) (S:Finset E4): Supply S h →ₗ[ℝ] G.Color:= ∑ x:(S:Set E4),∑ i:Fin (h+1), glean (A x i) ∘ₗ LinearMap.proj i ∘ₗ LinearMap.proj x
lemma carpet_tower (P : Supply S h) : carpet A h S P=∑ x:(S:Set E4),∑ i:Fin (h+1), glean (A x i) (P x i):=by simp [carpet,LinearMap.sum_apply]
lemma onCarpet (i : World G) (hi : i.1∈S ∧ i.2.1.1 ≤ h): carpet A h S (pronounce S h i)= available (A i.1 i.2.1.1) i.2.1.2:=by
  rw [carpet_tower, pronounce,dif_pos hi]; let x : (S:Set E4):=⟨i.1,hi.1⟩; let j:Fin (h+1):= ⟨i.2.1.1,by have:=hi.2; omega⟩; change (∑ z:(S:Set E4), ∑ k:Fin (h+1),glean (A z k) ((task h x j i.2.1.2) z k)) = _
  rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ x) (fun a _ e=>by simp [task,e]), Finset.sum_eq_single_of_mem j (Finset.mem_univ j) (fun a _ e=>by simp [task,e])]; simp [task]; rfl
lemma bill_rich (H : Good S h L): Rich (Snow.grams (bill A)) S h L:=by
  let X:= carpet A h S
  -- binary via inner with carpet
  let B : Binary S h := (LinearMap.compl₂ (innerₗ G.Color) X).comp X
  use B; intro i hi j hj; change (⟪bill A j,bill A i⟫:ℂ) = _ -- complex coercion?
  unfold bill; rw [rests]; split_ifs with hf; rw [← onCarpet A i (H i hi),← onCarpet A j (H j hj)]; rfl; rw [Complex.ofReal_zero]

lemma read_post (x:E4) (K:Fabric G) (p:poly (Paint G)) : Snow.eyes (bill A) K (post x p)= probe (motor (pump K) (A x)) (send p):=by
  unfold Snow.eyes; rw [convey]; apply YM.XSpace.Compat.read_once; intro z
  rw [shades,pumped,bill,relax]
lemma read_product (x:Points n) (f:Fin n→ WickPol G) (K:Fabric G): Snow.eyes (bill A) K (product x (fun i=> enroll (f i))) = ∏ i,probe (motor (pump K) (A (x i))) (f i):=by rw [product,_root_.map_prod]; simp_rw [read_post,recovers]
end YM.XSpace.Sample
