import YM.FVA2.MasterImage

/-!
# Mean-zero inversion ghost plane, apart from the root choice

Root subtraction is the inverse of throwing away the constant mode on this
plane. Handles also fixed sites (don't use 2x for those weights).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Inversion
open Function Set Finset Filter Lattice MS MS.Koszul MS.Swirl MS.Native MS.Orbit
open PertExtension PertExtension.Orb
open Matrix Ends ArrayMap Substitute Lag
open scoped Classical

variable {G:Gauge} {n:Side}
local notation "X"=> X_ G n
local notation "Y"=> Y_ G n
local notation "x_"=> Z G (OEdge n)
local notation "y_"=> Z G (Vert n)
local notation "Ux"=> FullX G n
local notation "Uy"=> FullY G n
local notation "P"=> incl G n
local notation "F"=> pin G n
local notation "M"=> fullM G n
local notation "r"=> reflectX G n
local notation "c"=> reflectY G n

lemma cast_scal {A B: Type} (U : Matrix A B ℝ) (u:ℝ) : intoC (u • U)= (u:ℂ) • intoC U := by ext; simp [intoC]
lemma cast_plus {A B : Type}(U V:Matrix A B ℝ) : intoC (U+V)=intoC U+intoC V := by ext; simp [intoC]

-- symmetric pull

def averageX (G:Gauge)(n:Side) : FullX G n →ₗ[ℝ] RootX G n where
   toFun A x := A x.val-A (Orb.reflect x.val)
   map_add' A B := funext fun i=> by simp only [Pi.add_apply]; abel
   map_smul' u A:= funext fun i=>by simp only [Pi.smul_apply, RingHom.id_apply, smul_sub]

def invertX : Ux→ₗ[ℝ] Ux where
  toFun t i := -t (Orb.reflect i)
  map_add' u v:= funext fun i=>by simp [add_comm]
  map_smul' u t := funext fun i=>by simp

lemma transposePinX (h:Even n.val) : (coordinate P)ᵀ=coordinate (averageX G n):= by
    refine chart_adj _ _ fun u v=>?_
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type (α₁:=OEdge n),sum_edges _ h]
    exact Finset.sum_congr rfl fun i _=> by
      simp_rw [projector_k, lifted u i, refl_lift h u i.val, lifted u i]
      simp only [ PiLp.neg_apply,neg_mul,Finset.sum_neg_distrib,← sub_eq_add_neg]
      unfold averageX; simp only [LinearMap.coe_mk,AddHom.coe_mk,PiLp.sub_apply,mul_sub,
        Finset.sum_sub_distrib]
lemma invertXX : intoC (coordinate (invertX (G:=G) (n:=n)))=r := by
    ext ⟨i,v⟩ ⟨j,w⟩; rw [intoC,map_apply,coordinate_apply,projector_k]
    change (↑((-priv (j,w) (Orb.reflect i)) v):ℂ)= _
    simp [priv, Pi.single_apply,baseC, reflectX,Jfun,invX,ite_and]; split_ifs <;> simp [*]

abbrev rootP (G:Gauge)(n:Side) : Matrix (X_ G n) (Z G (OEdge n)) ℂ:= intoC (coordinate (incl G n))
local notation "E"=> rootP G n
lemma E_wide (h:Even n.val) : Eᵀ*E=(2:ℂ) • 1:= by
    unfold rootP; rw [ ← into_transpose,transposePinX h, ← into_mul,← coordinate_mul,
      show averageX G n ∘ₗ P=(2:ℝ) • LinearMap.id from LinearMap.ext (fun u=> by funext i; change P u _ - P u _= _; rw [refl_lift h,lifted,sub_neg_eq_add]; exact (two_smul ℝ _).symm),coord_smul,coordinate_id,cast_scal,into_one,Complex.ofReal_ofNat]
lemma R_image (h: Even n.val) : invertX ∘ₗ P=P := LinearMap.ext (fun u=> by funext i; change -P u _ =_; rw [refl_lift h,neg_neg])
lemma E_r (h:Even n.val) : r*E=E:= by unfold rootP; rw [← invertXX,← into_mul, ← coordinate_mul,R_image h]
lemma R_wide (h:Even n.val): E*Eᵀ=1+r := by
    unfold rootP; rw [← into_transpose,transposePinX h,← into_mul,← coordinate_mul]
    have ht : P ∘ₗ averageX G n= LinearMap.id + invertX := LinearMap.ext (fun u=> by
        funext i; rcases eR_spec i with hI|hI
        · change P (averageX G n u) _=_; rw [lifted _ (⟨i,hI⟩:OEdge n)]; exact sub_eq_add_neg ..
        change P (averageX G n u) _=_
        rw [← neg_neg (P _ _),← refl_lift h,lifted _ (⟨Orb.reflect i,by rw [eR_reflect,hI]⟩:OEdge n)]; change -(u (Orb.reflect i)-u (Orb.reflect (Orb.reflect i)))=_; rw [Orb.reflect_reflect]; change _=u i+-u (Orb.reflect i); abel)
    rw [ht,coordinate_add,cast_plus, invertXX,coordinate_id,into_one]

-- site constant field harmonic.
def invertY : Uy →ₗ[ℝ] Uy where
   toFun x i:= x (-i)
   map_add' _ _:= rfl
   map_smul' _ _:=rfl

def meanY : Uy →ₗ[ℝ] Uy where
   toFun v _:= νt n • ∑ i:Site n,v i
   map_add' u v:= funext fun _ => by simp only [Pi.add_apply,Finset.sum_add_distrib,smul_add]
   map_smul' c₀ v:= funext fun i=> by simp only [Pi.smul_apply,← Finset.smul_sum, RingHom.id_apply,smul_comm (νt n) c₀]
def subtractY (G:Gauge)(n:Side): FullY G n→ₗ[ℝ] RootY G n where
   toFun v i:= v i.val-v 0
   map_add' v w := funext fun i=> by simp only [Pi.add_apply]; abel
   map_smul' v w := funext fun i=> by simp only [Pi.smul_apply,smul_sub]; rfl

local notation "D"=> subtractY G n
local notation "m"=> meanY (G:=G) (n:=n)
-- notation parser

lemma adjM1 : intoC (coordinate (invertY (G:=G) (n:=n)))=c := by
    ext ⟨i,u⟩ ⟨j,v⟩; simp only [intoC,map_apply,coordinate_apply,projector_k]; change (↑(priv (j,v) (-i) u):ℂ)=_; simp [reflectY,JY,Jfun,priv,flip_pY,Pi.single_apply,baseC,ite_and]; split_ifs <;> simp_all
lemma harm_mean : intoC (coordinate m)= HarmY := by
    ext ⟨i,u⟩ ⟨j,v⟩; rw [intoC,map_apply,coordinate_apply,projector_k]
    change (↑((νt n • ∑ k:Site n,priv (j,v) k) u):ℂ)= _; simp [priv,Pi.single_apply,HarmY,baseC]; split_ifs <;> simp [scaleZ,νt]
lemma gd_inter : r*M=M*c:= by
    unfold fullM; rw [← dGraph,← adjM1,← invertXX,← into_mul,← into_mul, ← coordinate_mul,← coordinate_mul]
    refine congr_arg (fun K=>intoC (coordinate K)) (LinearMap.ext fun v=>?_); funext i;
    change -((full n).flow 0 v (Orb.reflect i))=(full n).flow 0 (invertY v) i; rw [fullEnd0,fullEnd0];
    change -(v (-i.1-step i.2+step i.2)-v (-i.1-step i.2))=v (-(i.1+step i.2))- v (-i.1); rw [sub_add_cancel, show -i.1-step i.2= -(i.1+step i.2) from (by abel)]; abel
lemma E_Hx : r * (HarmX (G:=G) (n:=n))= -HarmX:= by rw [reflectX, neg_mul,leftJF]; apply congr_arg Neg.neg; ext i j; rfl
lemma C_Hy : c * (HarmY (G:=G) (n:=n))= HarmY:= by rw [reflectY,JY,leftJF]; ext; rfl
lemma pin_const (u:G.Color) : m (fun _:Site n=>u)=fun _=>u:= by
   funext x; change νt n • _=u; rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]; simp [νt,smul_smul]
lemma repeat_m : m ∘ₗ m=m:= LinearMap.ext fun _=>pin_const _
lemma m_invert : m ∘ₗ invertY=m:= by refine LinearMap.ext fun i=>?_ ; funext k; exact congr_arg (νt n • ·) (Equiv.sum_comp (Equiv.neg (Site n)) i)
lemma inline_m : invertY ∘ₗ m=m:=rfl
lemma no_const : M*(HarmY (G:=G) (n:=n))=0:= by
   unfold fullM; rw [ ← dGraph,← harm_mean, ← into_mul,← coordinate_mul, show (full n).flow 0 ∘ₗ m=0 from LinearMap.ext (fun i=> by funext k; change (full n).flow 0 _ _ = _; rw [ fullEnd0 ]; change m i _ - m i _=0; exact sub_self _),coord_zero,into_zero]
lemma discard_m : D ∘ₗ m=0:= LinearMap.ext fun _=> funext fun _=> (sub_self _)

def tallyY : RootY G n →ₗ[ℝ] Uy:= F - m ∘ₗ F
local notation "Q"=> tallyY (G:=G) (n:=n)
lemma backF : D ∘ₗ F=LinearMap.id:= by
   apply LinearMap.ext; intro i; funext k; change F i _-F i _= _; rw [pin_at,pin_zero,sub_zero]; rfl
lemma tally_inv : D ∘ₗ Q= LinearMap.id := by rw [tallyY,LinearMap.comp_sub, ← LinearMap.comp_assoc, discard_m,backF]; simp
lemma tally_m : m ∘ₗ Q=0 := by rw [tallyY, LinearMap.comp_sub,← LinearMap.comp_assoc,repeat_m,sub_self]
lemma pin_invert : invertY ∘ₗ F=F:= LinearMap.ext fun i=> funext (fun x=> pin_even i x)
lemma tally_even : invertY ∘ₗ Q=Q := by rw [tallyY,LinearMap.comp_sub,← LinearMap.comp_assoc,inline_m,pin_invert]
lemma restoration (A:Uy)(h:invertY A=A)(hk:m A=0): Q (D A)=A:= by
   have hh : F (D A)=A-fun (_:Site n)=>A 0 := by
     funext i; have hv : A (vertex i)=A i:= by rcases vertex_spec i with ht|ht <;> rw [ht]; exact congr_fun h i
     by_cases hz:vertex i=0
     · rw [hz] at hv; unfold pin; simp [locate,hz,hv]
     unfold pin; simp only [LinearMap.coe_mk, AddHom.coe_mk,locate,dif_neg hz,Option.elim_some]; change A (vertex i) -_ =_; rw [hv]; rfl
   rw [tallyY,LinearMap.sub_apply,LinearMap.comp_apply,hh,map_sub,hk,pin_const]; abel

abbrev Jbar (G:Gauge)(n:Side): Matrix (Y_ G n) (Z G (Vert n)) ℂ:= intoC (coordinate tallyY)
abbrev Jpast (G:Gauge)(n:Side): Matrix (Z G (Vert n)) (Y_ G n) ℂ := intoC (coordinate (subtractY G n))
local notation "J"=> Jbar G n
local notation "A"=> Jpast G n
lemma AJ : A*J=1:= by unfold Jpast Jbar; rw [← into_mul,← coordinate_mul,tally_inv,coordinate_id,into_one]
lemma even_J : c*J=J:= by unfold Jbar; rw [← adjM1,← into_mul,← coordinate_mul,tally_even]
lemma null_J : (HarmY (G:=G) (n:=n))*J=0:= by unfold Jbar; rw [ ← harm_mean,← into_mul,← coordinate_mul,tally_m,coord_zero,into_zero]
lemma norm_even : let V : Matrix Y Y ℂ:=(1+c)*(1-HarmY); J*A*V=V := by
   intro V
   let Z: Uy →ₗ[ℝ] Uy:= LinearMap.id + invertY
   let g: Uy →ₗ[ℝ] Uy:= Z ∘ₗ (LinearMap.id - m)
   rw [show V= intoC (coordinate g) from ?_]; swap
   · dsimp only [g,Z]; rw [coordinate_mul, coordinate_add, coord_sub, into_mul, coordinate_id,into_sub,cast_plus,into_one,adjM1,harm_mean] -- edit
   unfold Jbar Jpast; rw [← into_mul,← into_mul,← coordinate_mul,← coordinate_mul]
   have hv (i:Uy) : invertY (g i)=g i := by unfold g Z; simp only [LinearMap.comp_apply,LinearMap.add_apply,LinearMap.id_apply,map_add]; rw [show ∀ a:Uy,invertY (invertY a)=a from fun a=> by funext p; change a (- -p)=_; rw [neg_neg]]; abel
   have hx (i:Uy): m (g i)=0:= by unfold g Z; simp only [LinearMap.comp_apply,LinearMap.add_apply,LinearMap.id_apply,map_add]; rw [ show ∀ a:Uy,m (invertY a)=m a from fun a=> LinearMap.congr_fun m_invert a ]; rw [LinearMap.sub_apply,map_sub, show m (m _)=_ from LinearMap.congr_fun repeat_m i]; simp
   exact congr_arg (fun h=> intoC (coordinate h)) (LinearMap.ext fun i=> restoration (g i) (hv i) (hx i))

abbrev DM (G:Gauge)(n:Side): Matrix (Z G (OEdge n)) (Z G (Vert n)) ℂ:= intoC ((root n).gradientGraph (G:=G))
lemma J_deriv (h:Even n.val) : E*DM G n=M*J:= by
    unfold rootP DM Jbar tallyY; rw [← into_mul,lifted_gradient h,coord_sub,coordinate_mul, into_sub,into_mul,into_mul,Matrix.mul_sub, ←Matrix.mul_assoc _ (intoC (coordinate m)), harm_mean,no_const]; simp

end YM.FVA2.Inversion
