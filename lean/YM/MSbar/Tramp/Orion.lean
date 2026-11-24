import YM.MSbar.Tramp.Milk
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tramp
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Matrix
open Precision Gauge Midpoint Rolling Wave MvPolynomial Exterior Tree Wilson Laurent Bloch
open AnalyticBridge.VerifiedReset Native.Chart Tensor UVNext.PricedKernels
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge} {c n:Side}{S:StepData c n}(F: Forest S.ratio)
local notation "X"=> Primary n G
local notation "Y"=> Primary c G
local notation "T"=> S.ratio
local notation "O"=>path S.ratio G
local notation "Ω"=>address F G
local notation "K"=>Joint F G
local notation "φ"=>Key F G
local notation "θ"=> Measuring.chart n G
noncomputable def cardo (G:Gauge)(c:Side)(F:Forest S.ratio):=townCost G
variable (x: Positions (Primary c G))
local notation "D"=>(S.patch.L.val:ℝ)
-- Point prices with constructor issue billing.M
noncomputable def dripper (v: F.Free×G.ColorIndex): Primary n G:= primary v.1.val v.2
lemma era (v:Positions (Key F G)) (j:Key F G) : stamp F G v (dripper F j)= v j:=by rw [dripper,primary,ruler,dif_neg j.1.property]
lemma pivot (i:K)(j:φ): Rolling.straight F G i j= if i=Sum.inr j then 1 else 0:=by
    let V:= Rolling.straight F G; let f:Positions φ:= Pi.single j (1:ℝ); have he: lowerCol (ι:=Y) (τ:=Key F G) (bolt j)=bolt (Sum.inr j):= lower_bolt _
    have hx:f=(bolt j:Positions φ):=by ext i; by_cases he:i=j<;>simp [bolt,f,he]
    have hp : Rolling.straight F G*ᵥ f=bolt (Sum.inr j):=by rw [hx,Rolling.straight,LinearMap.toMatrix'_mulVec]; exact he
    have hv:= congrFun hp i; change (_*ᵥ (Pi.single j 1:_)) _=_ at hv; simp only [Matrix.mulVec_single,MulOpposite.op_one,one_smul, Matrix.col_apply] at hv; by_cases he:i=Sum.inr j<;>simpa [bolt,Pi.single_apply,he] using hv
lemma sail_cov (M:Matrix φ φ ℝ)(j i:K): let C:=Rolling.straight F G; (C*M*C.transpose) i j= match i,j with| Sum.inr i, Sum.inr j=> M i j | _, _ => 0:=by
    intro C; rw [Matrix.mul_apply]; simp_rw [Matrix.transpose_apply, Matrix.mul_apply, show ∀ i j,C i j= _ from pivot F]; cases i <;> cases j <;> simp [ite_mul,mul_ite]
variable (P:Cross S.ratio.count (TypeFace 1) (TypeFace 1))(R:PathData G)(p:Clip)(k:S.Choices)
variable (ρ:fieldDir G c 1→AxisChart G F) (h:Critical F p R ρ)(he:Guessed F (installed S.ratio P) ρ)
local notation "R!"=>installed T P
include h he
lemma ports (v:Y)(i:K) : poring F ρ i v=match i with| .inl i=> if i=v then 1 else 0 | .inr i=> shuttle F R! (dripper F i) v :=by
    let pT : Positions Y := Pi.single v 1; have hx:pT=bolt v:=by ext i;by_cases he:i=v<;>simp [bolt,pT,he]
    let u:= poring F ρ; have hq(i:K): u i v=throne F ρ pT i:=by rw [show throne F ρ pT=u*ᵥ pT from ?_]; unfold pT; simp [Matrix.mulVec_single]; unfold u poring; rw [LinearMap.toMatrix'_mulVec];rfl
    cases i with|inl i=> rw [show poring _ _ _ _= _ from hq (.inl i)]; change pT i=_; simp [pT,Pi.single_apply] -- maybe
                | inr i=> rw [show poring _ _ _ _= _ from hq (.inr i)]; change Rolling.center F ρ pT i=_; let pT₁:=Rolling.center F ρ pT; rw [← era F (Rolling.center F ρ pT) i, vaultT F R! pT ρ p R he h]; unfold pT; simp [Matrix.mulVec_single]
omit h he
variable {E a b C' δ:ℝ}{s:ℕ}
variable (ha:0<a)(ho:P.strip a C')(hx:0≤ C')
include ha ho hx h he
local notation "κ"=>tranche S.patch a C'
lemma stape (i: K)(j:Y): gained (a/D) (Ω i) (O j)* |poring F ρ i j| ≤ 1+κ:=by
   have hb:0≤κ:=funds0 P ha ho hx
   rw [ports F P R p ρ h he]; cases i with
   | inl i=> by_cases he:i=j
             · subst j; simp only [if_pos,abs_one,mul_one]; change gained _ (O i) (O i)≤ _; simp [gained,hb]
             simp [he]; linarith only [hb]
   | inr i=>
       let w:= dripper F i; have hp:= feet F P ha ho hx 1 (show (1:ℝ)∈ Set.Icc 0 1 from ⟨zero_le_one,le_rfl⟩) (Sum.inl w) j
       have hh: shuttle F R! w j= mouth F R! 1 G (.inl w) j:=by simp [mouth,plot]
       apply le_trans _ (hp.trans (le_add_of_nonneg_left zero_le_one)); change gained _ (slide G n (Sum.inl w)) _ *|shuttle F R! w j| ≤ _; rw [hh]
-- taps point price ∂~1.A.
end YM.MSbar.Tramp
