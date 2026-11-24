import YM.FVA2.OptimizeTwo
/-!
# Currency: integrate step quadratic after pullback of retained coarse fields & external toll

Base support needed for full-torus history reading: K-space can be smaller/different and
we re-evaluate an already charged Q. Ward invariance not assumed by these identities.
Use `withToll` as many levels as needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Tandem.Luggage
open Function Filter MeasureTheory PertExtension Precision
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.MultiGauge.Papers
open PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial GaussianScore PowerSeries
open MeasureTheory.Measure (IsAddHaarMeasure)
open scoped Topology ContDiff BigOperators Classical
variable {E F U K X:Type}[NormedAddCommGroup E][NormedAddCommGroup F][NormedAddCommGroup U][NormedAddCommGroup K][NormedSpace ℝ E][NormedSpace ℝ F][NormedSpace ℝ U][NormedSpace ℝ K]
variable [FiniteDimensional ℝ E][FiniteDimensional ℝ F][FiniteDimensional ℝ U][FiniteDimensional ℝ K]
variable (SpaceQ' : Quadratic (E×F))(hx:SpaceQ'.core.RespectsPrice)(q:Quadratic K) (u:K→ₗ[ℝ] F)
-- integrate E, even K empty
local notation "Θ" => Quadratic.RespectsPrice.inner hx
abbrev toward (u:K→ₗ[ℝ] F): E×K→ₗ[ℝ] E × F:= (LinearMap.id (R:=ℝ) (M:=E)).prodMap u
local notation "π"=> LinearMap.snd ℝ E K
def inherits : Quadratic (E × K):= Quadratic.addOn (Quadratic.drag (toward u) SpaceQ') (Quadratic.drag π q)
local notation "SpaceQ₀"=> inherits SpaceQ' q u
lemma toll (x s:E × K): (SpaceQ₀).P x s= SpaceQ'.P (toward u x) (toward u s)+ q.P x.2 s.2:=rfl
include hx
lemma money : ( Quadratic.core SpaceQ₀ ).P=(Θ).P:= by apply LinearMap.ext; intro i; apply LinearMap.ext; intro j; rw [Θ_r]; change (SpaceQ₀).P (i,0) (j,0)=_; rw [toll]; simp [toward]
lemma earned : ( Quadratic.core SpaceQ₀ ).RespectsPrice:= ⟨Θ,money SpaceQ' hx q u⟩
local notation "hs"=> earned SpaceQ' hx q u
local notation "Λ"=>Quadratic.RespectsPrice.inner hs
lemma balance : Λ=Θ:= Quadratic.RespectsPrice.pinpoints hs ( money SpaceQ' hx q u )
lemma chart (p:K) : Quadratic.skew SpaceQ₀ hs p=SpaceQ'.skew hx (u p):= by
     symm; apply optimize.only SpaceQ₀ hs; intro x; rw [toll]; simp only [toward,LinearMap.prodMap_apply,LinearMap.id_coe,id_eq,map_zero,add_zero]; exact RayScatter.square.cross_zero SpaceQ' hx (u p) x
local notation "Ψ"=> Quadratic.reduced SpaceQ₀ hs
local notation "Ξ"=>Quadratic.reduced SpaceQ' hx
lemma port (p r:K): (Ψ).P p r=(Ξ).P (u p) (u r)+ q.P p r:= by
    change (SpaceQ₀).P ((SpaceQ₀).skew hs p,p) ((SpaceQ₀).skew hs r,r)=_; rw [chart,chart,toll]; rfl
omit hx [NormedAddCommGroup E][NormedAddCommGroup F][NormedSpace ℝ E][NormedSpace ℝ F][FiniteDimensional ℝ F][FiniteDimensional ℝ E] in
lemma only_P {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X] (Q R:Quadratic X)(h:Q.P=R.P): Q=R:= by cases Q; cases R; congr
-- eliminate unused hx in this helper for Quadratic eq
lemma port_charge : Ψ= Quadratic.addOn (Quadratic.drag u Ξ) q := only_P _ _ (LinearMap.ext fun i=> LinearMap.ext fun j=> port SpaceQ' hx q u i j)

variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[IsAddHaarMeasure μ]
omit hx
lemma peel (SpaceQ:Quadratic (E×K))(g:SpaceQ.core.RespectsPrice) (a: Permit (E×K))(t:Permit K): SpaceQ.integrateP μ g (a * translation π t)=SpaceQ.integrateP μ g a * t:= by
    apply Subtype.ext; funext x; change _=(SpaceQ.integrateP μ g a).val x*t.val x; rw [Quadratic.integrateP_display,Quadratic.integrateP_display];
    change g.inner.average μ (fun b:E=> a.val (b+SpaceQ.skew g x,x)*t.val x)=_; unfold Law.average; simp only [mul_right_comm _ (t.val x), Pi.mul_apply]; rw [integral_mul_const]; ring -- rw before Pi
lemma pullAway (SpaceQ:Quadratic (E×K))(g:SpaceQ.core.RespectsPrice)(a:Ticket (E × K))(t:Ticket K):
     SpaceQ.uptake μ g (a * boost π t)=SpaceQ.uptake μ g a * t:= by
   apply PowerSeries.ext; intro n; unfold Quadratic.uptake throughPrice boost; simp only [AddMonoidHom.coe_mk,ZeroHom.coe_mk, coeff_mk,coeff_map,coeff_mul,LinearMap.toAddMonoidHom_coe,map_sum]; exact Finset.sum_congr rfl (fun i _=>peel μ SpaceQ g _ _)
include hx
lemma consume_κ (a:Permit (E × F)): Quadratic.integrateP SpaceQ₀ μ hs (translation (toward u) a) = translation u (SpaceQ'.integrateP μ hx a):= by
    apply Subtype.ext; funext i; change _=(SpaceQ'.integrateP μ hx a).val (u i); rw [ Quadratic.integrateP_display,Quadratic.integrateP_display, balance SpaceQ' hx q u]; rw [ chart SpaceQ' hx q u i]; rfl
local notation "Υ"=> Quadratic.uptake SpaceQ₀ μ hs
lemma entitled (A:Ticket ( E × F )) : (Υ) (boost (toward u) A) = boost u (SpaceQ'.uptake μ hx A):= by
    apply PowerSeries.ext; intro i; unfold boost Quadratic.uptake throughPrice; simp only [ AddMonoidHom.coe_mk,ZeroHom.coe_mk,coeff_mk,LinearMap.toAddMonoidHom_coe,coeff_map ]; exact consume_κ SpaceQ' hx q u μ _
lemma weigh (A:Ticket ( E × F ))(B:Ticket K) : (Υ) (boost (toward u) A * boost π B) = boost u (SpaceQ'.uptake μ hx A) * B:= by rw [pullAway,entitled]
end YM.FVA2.Tandem.Luggage
