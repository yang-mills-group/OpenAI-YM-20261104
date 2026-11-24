import YM.FVA2.StepPalette
/-!
# Schur complement exact reclosure with a spectator field

Now the last matrix can be singular. Needed to descend without ever asking for massless
terminal Gaussian on a full un-inverted torus. Composition for the actual Quadratic.uptake
and receipts proved including every spectator direction.Use for step identity (with true path
Hessian below).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Tandem
open Function Filter Topology MeasureTheory PertExtension Precision
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice
open PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial GaussianScore PowerSeries
open RayScatter RayScatter.square
open MeasureTheory.Measure (IsAddHaarMeasure)
open scoped Topology ContDiff BigOperators Classical
variable {E F U K X:Type}[NormedAddCommGroup E][NormedAddCommGroup F][NormedAddCommGroup U][NormedAddCommGroup K][NormedSpace ℝ E][NormedSpace ℝ F][NormedSpace ℝ U][NormedSpace ℝ K]
variable [FiniteDimensional ℝ E][FiniteDimensional ℝ F][FiniteDimensional ℝ U][FiniteDimensional ℝ K]

namespace optimize
variable (W: Quadratic (U×K))(hp:W.core.RespectsPrice)
local notation "Λ"=> Quadratic.RespectsPrice.inner hp
include hp
-- `cross_zero` uniqueness. full matrix on U positive.
omit [FiniteDimensional ℝ K] in
theorem only (u:U)(v:K)(h:∀ x:U,W.P (u,v) (x,0)=0) : u=W.skew hp v:= by
    let E:=W.skew hp v; suffices he:u-E=0 from sub_eq_zero.mp he;
    have hx: (Λ).P (u-E)=0:= LinearMap.ext (fun x=> by
        rw [← show W.core.P=(Λ).P from hp.choose_spec]; change W.P (u-E,0) (x,0)= _; rw [show (u-E,(0:K))=(u,v)-(E,v) from by simp, map_sub, LinearMap.sub_apply,h, RayScatter.square.cross_zero W hp v x, sub_zero ]; rfl)
    rw [ ← (Λ).solves (u-E), hx,map_zero ]; -- syntax
omit hp
end optimize

-- E first fast,F second fast,U full axis. idx maps (e,y) to U. K spectator.
variable (W:Quadratic (U×K))(χ:(E×F)≃ₗ[ℝ] U)(hp:W.core.RespectsPrice)
local notation "Θ" => Quadratic.RespectsPrice.inner hp

def expandGauge (χ:(E×F)≃ₗ[ℝ] U) : (E × (F × K))≃ₗ[ℝ] U×K:= (LinearEquiv.prodAssoc ℝ E F K).symm.trans (χ.prodCongr (LinearEquiv.refl ℝ K))
def innerV : Quadratic (E × (F× K)) := Quadratic.drag (expandGauge χ).toLinearMap W
local notation "α"=> innerV W χ
lemma same (x x':E)(y y':F)(z z':K) : (α).P (x,y,z) (x',y',z')=W.P (χ (x,y),z) (χ (x',y'),z') := rfl
lemma Θ_r (u:U)(x:U): (Θ).P u x = W.P (u,0) (x,0):= by rw [←show W.core.P=(Θ).P from hp.choose_spec]; rfl
local notation "Kx"=> fast Θ χ

include hp
lemma core_E : (Quadratic.core (innerV W χ)).P = (Kx).P:= by apply LinearMap.ext; intro x; apply LinearMap.ext; intro y; change W.P _ _=(Θ).P _ _; rw [Θ_r]; rfl
lemma stays : (Quadratic.core (innerV W χ)).RespectsPrice:= ⟨ Kx,core_E W χ hp ⟩
local notation "hpE"=> stays W χ hp
local notation "pE" => ( Quadratic.core α )
local notation "Ω"=> Quadratic.RespectsPrice.inner hpE
local notation "B"=> Quadratic.reduced α hpE
local notation "Ξ"=> Quadratic.skew α hpE
lemma price_E : Ω= fast Θ χ:= Quadratic.RespectsPrice.pinpoints hpE ( core_E W χ hp )
lemma property_u (y:F): pin Θ χ y = (Ξ) (y,0):= optimize.only α hpE _ (y,0) (fun e=> by
    obtain he:= Splice.orthogonal Θ χ e y; rw [Splice.namely, Θ_r] at he; exact he)
lemma stays_f : (Quadratic.core (Quadratic.reduced α hpE)).P=(rest Θ χ).P:= by
     apply LinearMap.ext; intro x; apply LinearMap.ext; intro y; change (α).P ((Ξ) (x,0),(x,0)) ((Ξ) (y,0),y,0)=(Θ).P (shaft Θ χ x) (shaft Θ χ y); rw [ ←property_u, ←property_u,same, Θ_r, Splice.namely, Splice.namely ]
lemma stays_second : (Quadratic.core (Quadratic.reduced α hpE)).RespectsPrice:= ⟨ rest Θ χ, stays_f W χ hp ⟩
local notation "hpF"=> stays_second W χ hp
local notation "Φ"=> Quadratic.RespectsPrice.inner hpF
local notation "ξ"=> Quadratic.skew B hpF
lemma price_F : Φ=rest Θ χ:= Quadratic.RespectsPrice.pinpoints hpF ( stays_f W χ hp )

-- tangent splitting at arbitrary spectator! Bigger currency.Engine
local notation "π"=> W.skew hp
variable (b:K)
lemma tandemL : (χ.symm ((π) b)).1= (Ξ) ( (χ.symm ((π) b)).2,b) := by
    let v:= (π) b; let X:=χ.symm v; apply optimize.only α hpE; intro x
    change W.P ( χ X,b ) _=_; rw [show χ X=v from χ.apply_symm_apply v]; exact RayScatter.square.cross_zero W hp b _
lemma tandemR : (χ.symm ((π) b)).2= (ξ) b:= by
    let X:=χ.symm ((π) b); apply optimize.only B hpF; intro x
    change W.P (χ ((Ξ) _, X.2), b) _=_; rw [ ← tandemL W χ hp, show χ ((χ.symm _).1,X.2)=(π) b from χ.apply_symm_apply ((π) b) ]; exact RayScatter.square.cross_zero W hp b _
lemma total_move : Quadratic.skew W hp b=χ ((Ξ) ((ξ) b,b),(ξ) b):= by
    apply χ.symm.injective; rw [LinearEquiv.symm_apply_apply]; refine Prod.ext ?_ (tandemR W χ hp b); change _= (Ξ) _; rw [tandemL, tandemR]
lemma readf (b:K)(c:K) : ( Quadratic.reduced B hpF ).P b c=( Quadratic.reduced W hp ).P b c:= by
    change (innerV W χ).P ((Ξ) ((ξ) b,b), (ξ) b,b) ((Ξ) ((ξ) c,c),(ξ) c,c)=W.P _ _; change _=W.P ((π) b,b) ((π) c,c); rw [ same,←total_move, ← total_move]
lemma start (u:E)(v:F): fusion Θ χ (u,v)+(π) b=χ (u+(Ξ) (v+(ξ) b,b),v+(ξ) b) := by
    have hf : (v+ (ξ) b,b)=((v,0): F × K)+((ξ) b,b) := by simp -- syntax
    rw [ fusion_eq, Splice.namely,total_move W χ hp, property_u, hf, map_add, show fine χ u=χ (u,0) from rfl, ← map_add, ← map_add ]; apply congr_arg; ext1 <;> simp only [ Prod.fst_add,Prod.snd_add,zero_add,add_zero ]; abel

-- normalization of Gaussian uptake of ANY ticket. Not yet dividing by income in this identity.
variable [MeasurableSpace U][BorelSpace U] [MeasurableSpace F][BorelSpace F] [MeasurableSpace E][BorelSpace E]
variable (μ:Measure U)[IsAddHaarMeasure μ] (η:Measure F) [IsAddHaarMeasure η](ν:Measure E)[IsAddHaarMeasure ν]
lemma push (g:Permit (U×K))(b:K):
    (W.integrateP μ hp g).val b= (Quadratic.integrateP B η hpF (Quadratic.integrateP α ν hpE (Papers.translation (expandGauge χ).toLinearMap g))).val b:= by
    let f(x:U):=g.val (x+(π) b,b); have he : f ∈ papers U:= by simpa [f] using! Papers.consign (d:=LinearMap.inl ℝ U K) ((π) b,b) g.property -- pair(x,0)+(p,b): defeq snd maybe?
    obtain ht:= splice_int Θ χ μ ν η f (Papers.useful μ Θ (Boson.minted he)); rw [Quadratic.integrateP_display,Quadratic.integrateP_display]; simp_rw [price_F W χ hp,Quadratic.integrateP_display,price_E W χ hp]; change (Θ).average μ f=_; rw [ht]; apply congr_arg ((rest Θ χ).average η); funext x; apply congr_arg ((fast Θ χ).average ν); funext v; unfold f; rw [start]; rfl

def inheritWithin (r:Ticket (U×K)): Ticket ( F×K):= Quadratic.uptake α ν hpE (boost (expandGauge χ).toLinearMap r)

lemma sew (r:Ticket (U×K)): W.uptake μ hp r= Quadratic.uptake B η hpF ( Quadratic.uptake α ν hpE (boost (expandGauge χ).toLinearMap r) ) := by
    apply PowerSeries.ext; intro i; apply Subtype.ext; funext x
    unfold Quadratic.uptake throughPrice boost; simp only [ PowerSeries.coeff_map,AddMonoidHom.coe_mk,ZeroHom.coe_mk, coeff_mk,LinearMap.toAddMonoidHom_coe ]; exact push W χ hp μ η ν ( coeff i r ) x
end YM.FVA2.Tandem
