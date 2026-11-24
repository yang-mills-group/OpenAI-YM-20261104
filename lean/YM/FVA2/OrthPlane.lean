import YM.FVA2.TermsOfGauge

/-!
# Real maps for the based orthogonal plane
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Inversion
open Function Set Finset Filter Lattice MS MS.Koszul MS.Swirl MS.Native MS.Orbit MS.Orbit.Cog
open PertExtension PertExtension.Orb
open Matrix Ends ArrayMap Substitute Lag
open scoped Classical Topology RealInnerProductSpace
variable {G:Gauge} {n:Side}
local notation "x_"=> Z G (OEdge n)
local notation "y_"=> Z G (Vert n)
local notation "Zr"=> baseFix G n
local notation "u"=> DM G n
local notation "r"=> (2:ℝ)⁻¹
local notation "E"=> rootP G n
local notation "J"=> Jbar G n
local notation "W"=> baseProp G n
abbrev gradR (G:Gauge)(n:Side) := flow (root n) (0:RootX G n)
local notation "M"=> gradR G n

lemma warm (h:Even n.val): (u*Zr)ᵀ=u*Zr := by
    obtain ⟨V,hV⟩:= landed (n:=n) (G:=G) h
    suffices ht : (u*Zr)*(u*Zr)ᵀ=(u*Zr)ᵀ by
      have hu:= congr_arg Matrix.transpose ht; rw [Matrix.transpose_mul,transpose_transpose] at hu; exact ht.symm.trans hu
    rw [transpose_mul,hV,← Matrix.mul_assoc, ← Matrix.mul_assoc,Matrix.mul_assoc u Zr u,gauge_left h]; simp
lemma protects (h:Even n.val) : (1-u*Zr)*W=W := by
    rw [ ← warm h, transpose_mul]; obtain ⟨X,hx⟩:= landed (G:=G) h -- maybe enough transverse
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc _ uᵀ, transverseW h]; simp
lemma masks (h: Even n.val) : Zr*(u*Zr)=Zr:= by rw [← Matrix.mul_assoc,gauge_left h]; simp

-- reify real map Zr. It is uniquely determined by the gradient and orthogonality (unlike arbitrary K ghost matrices)
def realF (G:Gauge)(n:Side) : RootX G n→ₗ[ℝ] RootY G n:=
    (LinearMap.toMatrix (baseChart G (OEdge n)) (baseChart G (Vert n))).symm
    ((baseFix G n).map Complex.re)
local notation "B"=> realF G n

lemma starJ {A Q R : Type} [Fintype Q] (Z:Matrix A Q ℂ)(G:Matrix Q R ℂ):
    (Z*G).map star=Z.map star * G.map star := by ext; simp [Matrix.mul_apply]
lemma star_one {A : Type}[DecidableEq A] : (1:Matrix A A ℂ).map star=1:=by ext; simp [Matrix.one_apply,apply_ite]
lemma starG : (u).map star=u := by ext; simp [DM,intoC]
lemma starTr (h:Even n.val) : (Zr).map star=Zr := by
    have hz:(Zr).map star*u=1:= by
      conv_lhs => rhs; rw [← starG]
      rw [← starJ,gauge_left h,star_one]
    have hx:(u*((Zr).map star))ᵀ=u* ((Zr).map star):= by
       have hv:= congr_arg (fun (A:Matrix x_ x_ ℂ) => A.map star) (warm (G:=G) h)
       change ((u*Zr)ᵀ).map star= (u*Zr).map star at hv; rw [Matrix.transpose_map,starJ,starG] at hv; exact hv
    let R:= (Zr).map star; let P:=u*R
    have hp : P=u*Zr := by
       have ht:P*(u*Zr)=u*Zr:= by unfold P; rw [← Matrix.mul_assoc,Matrix.mul_assoc u R u, show R*u=1 from hz]; simp
       have hf:(u*Zr)*P=P:= by unfold P; rw [← Matrix.mul_assoc,Matrix.mul_assoc u Zr u,gauge_left h]; simp
       apply hf.symm.trans
       have hm:= congr_arg Matrix.transpose ht; rwa [transpose_mul, show Pᵀ=P from hx, warm h] at hm -- inspect
    calc
      R= Zr*(u*R):= by rw [← Matrix.mul_assoc, gauge_left h]; simp
      _= _:= by rw [show u*R=_ from hp,masks h]
lemma C_in {A Q:Type} {V R:Matrix A Q ℝ}(h:intoC V=intoC R) : V=R:= by
    ext i j; exact Complex.ofReal_injective (congr_fun (congr_fun h i) j)
lemma into_fix (h:Even n.val) : intoC (coordinate B)=Zr := by
    rw [coordinate, realF, LinearEquiv.apply_symm_apply]; ext i j
    obtain ht:= congr_fun (congr_fun (starTr (G:=G) h) i) j
    apply Complex.ext; rfl; have hq : -(Zr i j).im=(Zr i j).im:= congr_arg Complex.im ht; change 0=_; linarith
lemma grad_complex : intoC (coordinate M)=u:= by rw [gradR, dGraph]
lemma left_real (h:Even n.val) : B ∘ₗ M= LinearMap.id:= by
    apply coordinate_inj; apply C_in; rw [coordinate_mul,into_mul, coordinate_id, into_one,into_fix h,grad_complex,gauge_left h]

def plane : RootX G n→L[ℝ] RootX G n:= (M ∘ₗ B).toContinuousLinearMap
def transP : RootX G n→L[ℝ] RootX G n := ContinuousLinearMap.id ℝ (RootX G n)-plane
set_option quotPrecheck false
local notation "L"=> (coordinate (plane (G:=G) (n:=n)).toLinearMap)
local notation "F"=> (coordinate (transP (G:=G) (n:=n)).toLinearMap)
lemma orthoP (h:Even n.val): intoC L=u*Zr:= by change intoC (coordinate (M∘ₗ B))=_; rw [coordinate_mul,into_mul,into_fix h,grad_complex]
lemma scale_transP (h: Even n.val): intoC F=1-u*Zr:= by
    change intoC (coordinate (LinearMap.id-(plane (G:=G) (n:=n)).toLinearMap))=_; rw [coord_sub,coordinate_id,into_sub,into_one,orthoP h]
lemma vanish_t (h:Even n.val): (coordinate M)ᵀ * F=0:= by
    apply C_in; rw [into_mul,into_transpose,grad_complex, scale_transP h,into_zero]; apply Matrix.transpose_injective
    rw [Matrix.transpose_mul, transpose_transpose,transpose_sub,transpose_zero,transpose_one, warm h,Matrix.sub_mul, Matrix.one_mul,Matrix.mul_assoc,gauge_left h, Matrix.mul_one, sub_self]

-- inserted gauge symbol functional tests
variable {A : Type} [Fintype A]
def chartPair (g k: Lot G A) := ∑ i : Z G A, projector i g * projector i k
lemma grid_pair (g k: Lot G A) : chartPair g k = ∑ i:A,@inner ℝ _ _ (g i) (k i) := by
    unfold chartPair; rw [ Fintype.sum_prod_type ]; refine Finset.sum_congr rfl fun i _=> ?_
    simp_rw [projector_k]; rw [PiLp.inner_apply]; exact Finset.sum_congr rfl (fun k _=> mul_comm ..) -- inspect
lemma base_pair (a b:RootX G n)(h:Even n.val) : chartPair (incl G n a) (incl G n b)=2*chartPair a b:= by
    rw [grid_pair,grid_pair,sum_edges _ h]; simp_rw [lifted,refl_lift h, lifted, inner_neg_neg,two_mul,Finset.sum_add_distrib]
lemma vanish_inner (h:Even n.val) (a:RootX G n)(b:RootY G n) : chartPair (M b) (transP a)=0:= by
    have hu(b:y_)(a:x_): chartPair (M (priv b)) (transP (priv a))=0 := by
       have hx:=vanish_t (G:=G) h; have hz:=(congr_fun (congr_fun hx b) a)
       simp_rw [Matrix.mul_apply,transpose_apply,coordinate_apply] at hz; exact hz
    unfold chartPair
    rw [← Native.frame b, ← Native.frame a]; simp_rw [map_sum,map_smul,smul_eq_mul,
       Finset.sum_mul, Finset.mul_sum, show ∀ i j k, projector i b * (projector j) (M (priv i)) * (projector k a * (projector j) (transP (priv k))) = (projector i b * projector k a) * ((projector j) (M (priv i))* (projector j) (transP (priv k))) from fun i j k=> by ring]
    rw [Finset.sum_comm]; refine Finset.sum_eq_zero fun i _=>?_; rw [Finset.sum_comm]; refine Finset.sum_eq_zero fun j _=> ?_
    rw [← Finset.mul_sum,show ∑ k: Z G (OEdge n),projector k (M (priv i))*projector k (transP (priv j))=0 from hu i j,mul_zero]
-- Adjoint rotates such that any gradient stays orthogonal to the image
lemma rotate_grad (i:G.El)(b:RootY G n): M (fun v=> G.adjoint i (b v))= fun x=> G.adjoint i (M b x) := by
    funext x; simp_rw [gradR, rootEnd0,map_sub]; congr! 1 <;> (unfold pin; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; cases locate (x.val.1+step x.val.2) <;> cases locate x.val.1 <;> simp)
lemma adj_pair (h:Even n.val)(a b:RootX G n)(i:G.El) : chartPair (plane b) (fun x=> G.adjoint i (transP a x))=0:= by
    let j:= fun x=> G.adjoint i⁻¹ (B b x)
    have hx := vanish_inner h a j; rw [grid_pair] at hx; rw [grid_pair]; apply Eq.trans _ hx
    refine Finset.sum_congr rfl fun x _=>?_; rw [show M j = _ from rotate_grad i⁻¹ (B b)];
    let S : G.Color→ₗᵢ[ℝ] G.Color:={G.adjoint i with norm_map':= G.norm_adjoint i}
    have ht:= S.inner_map_map ((fun x=>G.adjoint i⁻¹ (M (B b) x)) x) (transP a x); rw [show S _=plane b x from ?_] at ht; exact ht
    change G.adjoint i (G.adjoint i⁻¹ _)= M (B b) x; rw [← G.adjoint_mul,mul_inv_cancel,G.adjoint_one]
lemma plane_read (v : RootX G n)(i:G.El): (fun x=> G.adjoint i (incl G n v x))= incl G n (fun x=> G.adjoint i (v x)):= by funext x; unfold incl; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; split <;> simp [*]

end YM.FVA2.Inversion
