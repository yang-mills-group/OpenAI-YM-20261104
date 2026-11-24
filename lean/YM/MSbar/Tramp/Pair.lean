import YM.MSbar.Tramp.Syringe
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tramp
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Wave MvPolynomial
open Matrix
open AnalyticBridge.VerifiedReset Native.Chart Tensor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable (G:Gauge)(n: Side)
local notation "Π!"=>Positions (Primary n G)
local notation "A"=> Primary n G
local notation "Ω"=> Positions (Cards G n)
local notation "T"=> cards0 G n
local notation "H"=>cardsH G n
local notation "U"=> slide G n
local notation "L"=> Measuring.chart n G
local notation "p!"=>Cacao.Pot A
noncomputable def hinge (G:Gauge)(n:Side)(f:Primary n G): Cards G n:=Sum.inr (Sum.inr f)
def Ipen (G:Gauge)(n:Side)(g:Cards G n)(p:Cards G n) : ℝ:=match g with
    | Sum.inl i=>if p= .inr (.inr i) then 1 else 0
    | Sum.inr _=>0
lemma inkSpot (m:ℕ) (a:ℝ) : LoopNet (slide G n) a m (Ipen G n) 1:=by
    refine ⟨zero_le_one,fun i=>?_,fun i=>?_⟩
    · cases i <;> simp [Ipen,liftW,slide,apply_ite abs,ite_mul]
    cases i with
    | inl i=> simp [Cards,Fintype.sum_sum_type,Ipen]
    | inr i=> cases i with
              | inl i=>simp [Cards,Fintype.sum_sum_type,Ipen]
              | inr i=> unfold Cards; rw [Fintype.sum_sum_type]; simp [Ipen,Fintype.sum_sum_type,slide,apply_ite abs,ite_mul,liftW]
noncomputable def sieve (G:Gauge)(n:Side)(Z : Cacao.Pot (Primary n G)):Pot (Cards G n):= Rolling.rail (LinearMap.toMatrix' (cards0 G n).toLinearMap) Z
lemma href (Z: Cacao.Pot (Primary n G)) (x:Positions (Cards G n)): clue (sieve G n Z) x = clue Z (cards0 G n x):=by
    have he:= congr_fun (clearL (LinearMap.toMatrix' (cards0 G n).toLinearMap) x) Z; change _= (MvPolynomial.eval ((LinearMap.toMatrix' (cards0 G n).toLinearMap)*ᵥ x)) Z at he; rw [LinearMap.toMatrix'_mulVec] at he; exact he
lemma sipped (Z:Cacao.Pot (Primary n G))(a:ℝ)(k s:ℕ){C':ℝ}(hp:Tokew (Measuring.chart n G) a s k 0 Z C')(ha:0 ≤ a): Tokew (slide G n) a s k 0 (sieve G n Z) C':=by
   let K:=LinearMap.toMatrix' (cards0 G n).toLinearMap
   have hv (j:A) (i:Cards G n): K j i= if i=Sum.inl j then 1 else 0:=by
       let w:Ω:= Uniform.bolt i; have h:T w j= if i= Sum.inl j then 1 else 0:=by change w (.inl j)= _; by_cases he:i=.inl j <;> simp [bolt,w,he,Ne.symm]
       have ht: w=(Pi.single i 1:Ω):= by ext k;by_cases he:k=i<;>simp [bolt,w,he]
       rw [ht] at h; have hx: T (Pi.single i 1) j= K j i:=by rw [show T (_:Ω) j=(K*ᵥ Pi.single i 1) j from (congrFun (LinearMap.toMatrix'_mulVec (cards0 G n).toLinearMap _).symm j)]; simp [Matrix.mulVec_single]
       exact hx.symm.trans h
   have h0(i:A):skim L U a s i (Sum.inl i)=1:=by unfold skim slide; rw [Sum.elim_inl,separation_self,Nat.cast_zero,mul_zero]; unfold Measuring.factor; simp -- ambiguous
   have hX : Syrup L U a s K 1:=by
        refine ⟨le_rfl,fun i=>?_,fun j=>?_⟩ <;> simp_rw [hv]
        · rw [Finset.sum_eq_single (.inl i)]; rw [if_pos rfl,abs_one,h0,mul_one];intro j _ hx; simp only [if_neg hx,abs_zero,mul_zero];simp
        cases j <;> simp [apply_ite abs,mul_ite,h0]
   have he:Tin L a s k 1 Z C':=Tin.it zero_lt_one (Tin.lit (w:=1) zero_lt_one le_rfl hp) (by simp) le_rfl
   have ht:= (Tin.scaleT hX ha zero_lt_one he); apply Tokew.delta (Tin.weightTok zero_lt_one le_rfl ht) le_rfl (by simp) -- syntax
variable (i:Primary n G)(x:Positions (Cards G n))(k:ℕ)
local notation "J"=>hinge G n
lemma projection1 (v: Primary n G): T (bolt (.inl v))=bolt v:=by ext i; change bolt (.inl v:Cards G n) _= _; by_cases he:i=v<;> simp [he,bolt, Ne.symm]
lemma projectionH (v:Primary n G) : T (Uniform.bolt (hinge G n v))=0∧ cardsH G n (Uniform.bolt (hinge G n v))=0:=by
    constructor; ext i; change (bolt _) (Sum.inl i)= (0:ℝ); simp [bolt,hinge]
    ext i j; change (bolt (J v)) (Sum.inr (Sum.inl (i,j)))=(0:ℝ); simp [bolt,hinge]
lemma anchorD : clue (MvPolynomial.pderiv (J i) (light G n k)) x= choir k (H x) (T x) i:=by
   let f:=clue (light G n k); let I:=bolt (J i); rw [← tabs]; change fderiv ℝ f x I= _
   let g(t:ℝ):= x+t • I; set A₀:= (choir k (H x) (T x) i); have he:g 0=x:=by simp [g]
   let F(i:Primary n G):= choir k (H x) (T x) i; have hz:T I=0:=(projectionH G n i).1; have hh:H I=0:=(projectionH G n i).2
   have hc (t:ℝ): f (g t)= f x + t*F i:=by
       unfold f light clue; rw [_root_.map_sum,_root_.map_sum]; let w(i:Primary n G):=auroraS G n k i; let z(j:Primary n G):= if j=i then t*F i else 0
       rw [show t*F i=∑ h,z h from (by unfold z; simp),←Finset.sum_add_distrib]
       refine Finset.sum_congr rfl fun j _=>?_ ; rw [show MvPolynomial.eval _ _= _ from sprite G n k j (g t),show MvPolynomial.eval x _ = _ from sprite G n k j x] -- sprite lhs clue not syntactic; check
       unfold iridesce g; rw [map_add,map_smul,hh,smul_zero,add_zero,map_add,map_smul,hz,smul_zero,add_zero]; unfold z; by_cases he:j=i<;>simp [he, I,bolt,hinge,F]; ring
   have hR:HasDerivAt g I 0:=by simpa only [g,one_smul, zero_add,zero_smul] using! ((hasDerivAt_id' (0:ℝ)).smul_const I).const_add x
   have ht:=((helm (light G n k) 1).differentiable (by simp) (g 0)).hasFDerivAt.comp_hasDerivAt 0 hR; rw [he] at ht; have hd : HasDerivAt (fun t:ℝ=> f (g t)) (F i) 0:=by rw [funext hc]; simpa only [one_mul] using! ((hasDerivAt_id' (0:ℝ)).mul_const (F i)).const_add (f x)
   exact ht.unique hd
end YM.MSbar.Tramp
