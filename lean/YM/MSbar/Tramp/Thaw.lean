import YM.MSbar.Tramp.Jet
import YM.UVNext.PRICED_KERNELS.Read
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tramp
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Matrix
open Precision Gauge Midpoint Rolling Wave MvPolynomial Exterior Tree Wilson
open AnalyticBridge.VerifiedReset Native.Chart Tensor UVNext.PricedKernels
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{c n: Side}{S:StepData c n} (F: Forest S.ratio)
local notation "Π!"=>Positions (Primary n G)
local notation "A"=> Primary n G
local notation "Ω"=> Positions (Cards G n)
local notation "T₀"=> cards0 G n
local notation "H"=>cardsH G n
local notation "U"=> slide G n
local notation "L₀"=> Measuring.chart n G
variable (R: Matrix (Body 1 n) (Body 1 c) ℝ) (x: Positions (Primary c G))(i: Primary n G)
noncomputable def runner (R:Matrix (Body 0 n) (Body 1 c) ℝ) (G:Gauge) : Matrix (Tramp.Block G n) (Primary c G) ℝ:= of (fun i j=> if i.2=j.2 then R (i.1,vac) j.1 else 0)
noncomputable def maple (G:Gauge) : Matrix (Primary n G) (Primary c G) ℝ := of (fun i j=> if i.2=j.2 then R i.1 j.1 else 0)
noncomputable def shuttle (F: Forest S.ratio) (R:Matrix (Body 1 n) (Body 1 c) ℝ) := maple (extracted S F R) G
-- shadow binder G.Syntax.S
lemma oak (i:Site n)(j:G.ColorIndex): (runner (straighten S F R) G *ᵥ x) (i,j)=(straighten S F R *ᵥ Exterior.parts G 1 (tint G _ x) j) (i,vac):=by
    unfold mulVec dotProduct runner; rw [Fintype.sum_prod_type]; simp [ite_mul,Exterior.parts,tint] -- names
lemma rad : (maple R G *ᵥ x) i=(R *ᵥ Exterior.parts G 1 (tint G _ x) i.2) i.1:=by unfold Matrix.mulVec dotProduct; rw [Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun j _=>?_ ; simp only [maple,of_apply]; simp [ite_mul,Exterior.parts,tint] -- test
lemma draft (s:Site n→G.Color): grad s i= (gradient s (rope i)) i.2:=by
    let F:= panel G n; rw [← (show F (grad s)= gradient s from F.apply_symm_apply _)]; change grad s i= grad s (primary (rope i) i.2); rw [curr]
lemma euclid : (shuttle (G:=G) F R*ᵥ x - maple R G *ᵥ x) = grad (tint G _ (runner (straighten S F R) G *ᵥ x)):=by
    let v(j):=(straighten S F R*ᵥ Exterior.parts G 1 (tint G _ x) j); let L:=shuttle (G:=G) F R
    funext i; unfold shuttle; rw [Pi.sub_apply,rad,rad,draft,extracted, Matrix.add_mulVec,← mulVec_mulVec];
    obtain ⟨⟨i,j⟩,y⟩:=i; obtain ⟨z,rfl⟩:= Exterior.axisEquiv.surjective j; change (_+ (d 0 n *ᵥ v y) (i,coord z))-_ =_
    rw [add_sub_cancel_left,d_sites]; unfold AnalyticBridge.VerifiedReset.gradient; simp only [PiLp.sub_apply, show rope ((i,axisEquiv z),y)=(i,z) from curb (i,z) y]; -- slides
    change v y (_,_) - _= (runner _ _*ᵥ x) _ - (runner _ _ *ᵥ x) _; congr 1; exact (oak F R x (i+step z) y).symm; exact (oak F R x i y).symm
variable (η:fieldDir G c 1→ AxisChart G F) (t:S.Choices) (p:Clip) (P:PathData G)
variable (h:Guessed F R η) (he:Critical F p P η)
include h he
lemma capSys (v:F.Free)(j:G.ColorIndex): center F η x (v,j)=(extracted S F R *ᵥ Exterior.parts G 1 (tint G _ x) j) (v.val.1,Exterior.coord v.val.2):=by
    let L:= tint G (Body 1 c); let N:= tint G F.Free; let g:= lyricP F η
    have hg: ContDiffAt ℝ ω g 0:= N.symm.contDiff.contDiffAt.comp (0:Positions (Primary c G)) ((show ContDiffAt ℝ ω η (L 0) from (map_zero L).symm ▸ he.2.1).comp _ L.contDiff.contDiffAt)
    have hv : fderiv ℝ g 0 x = N.symm (relative F R (L x)):=by
        let ξ:= relative F R (L x); let y:ℝ→Positions (Primary c G):=fun t=>t • x; have H₁:HasDerivAt y x 0:=by simpa using ((hasDerivAt_id' (0:ℝ)).smul_const x)
        have hs:g ∘ y= N.symm ∘ (fun t:ℝ=> η (t • L x)):=by funext t; unfold Function.comp g y lyricP; rw [map_smul]
        have hh: y 0=0:=zero_smul ..; rw [←hh] at hg; have hf:= (hg.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 H₁; rw [hh,hs] at hf; exact hf.unique (N.symm.hasFDerivAt.comp_hasDerivAt 0 (h (L x)))
    unfold Rolling.center; rw [_root_.add_apply, show fderiv ℝ (lyricP F η) _ _=_ from hv]
    let a:=(extracted S F R *ᵥ Exterior.parts G 1 (tint G _ x) j) (v.val.1,Exterior.coord v.val.2)
    change a-linearCopy S.ratio (collect G (tint G _ x)) v.val j + imageCopy F G x (v,j)=a; rw [sealShift, sub_add_cancel]; exact 0 -- x,y argument inspect
lemma vaultT : stamp F G (center F η x)= shuttle (G:=G) F R*ᵥ x:=by
    funext i; unfold shuttle; rw [rad]; obtain ⟨⟨i,b⟩,j⟩:= i; obtain ⟨b,rfl⟩:= axisEquiv.surjective b; change stamp F G _ ((i,Exterior.coord b),j)=_
    rw [ruler]; split; next hp=> exact (Precision.stays F R (Exterior.parts G 1 (tint G _ x) j) _ hp).symm
    next hv=> exact capSys F R x η p P h he ⟨_,hv⟩ j
end YM.MSbar.Tramp
