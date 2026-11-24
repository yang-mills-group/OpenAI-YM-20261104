import YM.MSbar.Duel.Rose
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Duel
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Further.GaussianScalar
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Tree
variable {G:Gauge}{c f:Side}{S:StepData c f}(F:Forest S.ratio) (R T:PathData G)(p q:Clip)(u:S.Choices) (ρ:fieldDir G c 1→AxisChart G F) (γ:ChartRatio G)
local notation "Π!"=>Primary c G
local notation "φ"=>Key F G
local notation "X"=> Joint F G
local notation "W"=> Positions (Primary c G)
local notation "J"=> Positions (Key F G)
local notation "L"=> Positions (Joint F G)
local notation "K"=> Push.Uniform.block (priced F u p R) 0
local notation "μ"=> PowerSeries.coeff
local notation "Y"=> center F ρ
local notation "i!"=> ink c q T
noncomputable def hands (F :Forest S.ratio)(G:Gauge) (i:Primary c G) : Positions (Joint F G):= meetVar (bolt i) (0:Positions (Key F G))
noncomputable def stampD (F: Forest S.ratio)(i: S.Choices)(G:Gauge) (v: Primary c G) : Pot (Joint F G):= -(dint (hands F G v) (potter (pushChart F G i) 2))
local notation "Δ"=>stampD F u G
local notation "I"=>hands F G
local notation "A"=>poring F ρ
local notation "C"=>straight F G
lemma meetE (x:Positions (Primary c G))(y:Positions (Key F G)) : present A C x y=meetVar x (center F ρ x+y):=by
    unfold present poring Rolling.straight; rw [LinearMap.toMatrix'_mulVec,LinearMap.toMatrix'_mulVec]; change (partSpace (Primary c G) _).symm (x,center F ρ x)+(partSpace (Primary c G) _).symm (0,y)= (partSpace _ _).symm (x,_); rw [← map_add, Prod.mk_add_mk,add_zero]
variable (h: S.patch.Branches S.kernel G)(hp: Premier (main f p R))(he: Critical F p R ρ)(ht:ClassicalMatch F p q R T ρ) (hx: Matrix.PosDef (Push.Uniform.block (priced F u p R) 0))
include hp he ht h hx
lemma edgesK : Mold (poring F ρ) (straight F G) (show Matrix (Key F G) (Key F G) ℝ from K⁻¹) (hands F G) (fun i=> center F ρ (bolt i)) (ink c q T) (stampD F u G):=by
    have hp₀:=pierce F u R T p q ρ h hp he ht
    constructor
    · intro i; unfold hands poring Rolling.straight; rw [LinearMap.toMatrix'_mulVec,LinearMap.toMatrix'_mulVec]; change (partSpace (Primary c G) _).symm _+(partSpace _ _).symm (0,center F ρ _)=(partSpace _ _).symm (_, _); rw [←map_add,Prod.mk_add_mk,add_zero,zero_add]; rfl
    intro i x y; let a:= Y x+y; let v:= meetVar x a; let b:= I i; let j:=potter (pushChart F G u) 2; let H(x:W):= eval x (i!)
    have hz(u:W): height c q T u= H u:=by
        let k':=(tint G (Body 1 c)).toContinuousLinearMap; unfold H ink; rw [pots]; change _=Tensor.diagonal (Tensor.coeff (main c q T ∘ k') 2 0) u; rw [show Tensor.diagonal _ u=_ from (hp₀.line k').second u,height,hp₀.second, show rim _ u u=_ from hp₀.carriage k' u u];rfl -- args
    let G'(t:ℝ):= x+t • bolt i; let f':= fun t:ℝ=> y - t • Y (bolt i); let L'(t:ℝ):=v+t •b; have hJ: (K).transpose=K:=by simpa [Matrix.IsHermitian] using hx.1 -- local notation apply
    let k:= Y (bolt i); let K':Matrix (Key F G) (Key F G) ℝ:=K; let w(s:J):= dotProduct s (K'*ᵥ s)/ (2:ℝ); let B:= dotProduct (K'*ᵥy) k
    have hF: HasDerivAt (fun t:ℝ=>w (f' t)) (-B) 0:=by
         have he: dotProduct y (K'*ᵥk)=B:=by unfold B; rw [dotProduct_mulVec,←Matrix.mulVec_transpose,hJ]
         have hX(t:ℝ):w (f' t)= w y -(B*t)+w k*t^2:=by
              unfold w f'
              change dotProduct (y - t • k) (K' *ᵥ (y - t • k)) /2=_; simp only [Matrix.mulVec_sub,Matrix.mulVec_smul,dotProduct_sub,sub_dotProduct,dotProduct_smul,smul_dotProduct,smul_eq_mul]; rw [he, dotProduct_comm k (K' *ᵥ y)]; unfold B; ring
         rw [funext hX]; convert! (hasDerivAt_const _ (w y)).sub ((hasDerivAt_id' 0).const_mul B) |>.add ((((hasDerivAt_id' (0:ℝ)).pow 2).const_mul (w k))) using 1; simp
    let J'(t:ℝ):=eval (L' t) j; let H'(t:ℝ):=H (G' t); have hv(t:ℝ) : J' t=H (G' t) + w (f' t)-height f p R (stamp F G a):=by
          have ha(t): center F ρ (G' t)+f' t=a:=by unfold G' f' a; rw [map_add,map_smul];abel
          have hb(t:ℝ): meetVar (G' t) a=L' t:=by unfold L' v b G' hands; unfold meetVar; rw [← map_smul,← map_add]; change _= (partSpace _ _).symm (x+t • bolt i,a+t • 0); rw [smul_zero,add_zero]
          have hx:= steady F u R T p q ρ h hp he ht (G' t) (f' t)
          unfold J' L'; unfold j; rw [pots]; apply eq_sub_of_add_eq'; rw [show center F ρ (G' t)+ _= a from ha t] at hx; dsimp only at hx; rw [hb,hz] at hx; exact hx
    have hp:HasDerivAt L' b 0:=by simpa only [zero_smul,one_smul,zero_add,add_zero] using (((hasDerivAt_id' (0:ℝ)).smul_const b).const_add v); -- syntax
    have he:HasDerivAt G' (bolt i) 0:=by simpa only [zero_smul,one_smul,zero_add,add_zero] using (((hasDerivAt_id' (0:ℝ)).smul_const (bolt i)).const_add x)
    have hB : HasDerivAt H' (eval x (dint (bolt i) (i!))) 0:=by
          have hq:= ((vent (i!)).differentiable (by simp) (G' 0)).hasFDerivAt.comp_hasDerivAt (0:ℝ) he; rw [dimY,show G' 0=x from (by unfold G'; simp)] at hq; exact hq
    have hk : HasDerivAt J' (eval v (dint b j)) 0:=by
          have hq:= ((vent j).differentiable (by simp) (L' 0)).hasFDerivAt.comp_hasDerivAt (0:ℝ) hp; rw [dimY,show L' 0=v from (by unfold L'; simp)] at hq; exact hq
    have hC : MvPolynomial.eval v (dint b j)=eval x (dint (bolt i) (i!))+ -B:= hk.unique (funext hv |>.symm ▸ ((hB.add hF).sub_const _))
    rw [show _+ C *ᵥ y=v from meetE F ρ x y]; unfold stampD; rw [_root_.map_neg, show MvPolynomial.eval v (dint (hands F G i) _) = _ from hC]; change _= _ + dotProduct (K'⁻¹⁻¹*ᵥ y) k; rw [nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hx.det_pos.ne')]; unfold B K'; abel
end YM.MSbar.Duel
