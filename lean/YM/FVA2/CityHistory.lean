import YM.FVA2.ShadowPort
import YM.RGComparison.Core16.Wick
/-!
# Keep the optional full-torus (cover) multilevel conditioning program in the same formal coordinates

For the comparison task toward the analytic estimates.Purely formal result.Never take massless terminal Gaussian
on this cover system. Use **precisely Descent**, including all its primitive penalties and unscaled Link-Haar charts.
Prices: Descent.account, Connect(Vander) weights along tree slice with all tag and probability factors.
We'll apply on admissible primitive histories with same gauge/fixed branches as our seat. Since users may choose
coupling ratios, after this file extend to embody arbitrary coupled clocks relative top. This file spells Hessian.
BlockGauge.Fabric is inversion-oriented distinct path (not automatically equality here).
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.CityHistory
open Function Filter Set Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice
open Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage
open MeasureTheory.Measure (IsAddHaarMeasure)
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius

variable {G:Gauge} {c f n : Side}
abbrev Pins (G:Gauge)(n:Side):= Direction G (Edge (Site n))
abbrev SpaceF (G:Gauge)(d:Descent n c):= (Coordinates G d) × Pins G c

abbrev axesP (G:Gauge)(n:Side) : Pins G n→L[ℝ] Push.In G n:= LinearMap.toContinuousLinearMap (LinearMap.pi fun i=>LinearMap.proj (i.1,axisEquiv.symm i.2))
lemma direct_link (u:Pins G c) : represent (axesP G c u)=expLinks G _ u:= by
     ext1 i; unfold represent RG.increment; change G.lieExp ((axesP G c u) _) * (1:G.El)= G.lieExp _; rw [mul_one]; change G.lieExp (u (i.1,axisEquiv.symm (Exterior.coord i.2)))=_; rw [← Exterior.coord_map, Equiv.symm_apply_apply ]

variable (d: Descent n c)(Z:ChartRatio G)(t:d.Tags)

def consume (b:ℕ→ℝ)(x:SpaceF G d):= d.account b t (expLinks G _ x.2) (d.tablePath x.1)
local notation "H"=> consume d t (G:=G)
lemma thermal (h:d.OK G)(b:ℕ→ℝ): ContDiffAt ℝ ω (consume d (G:=G) t b) 0:= by
     unfold consume; simp_rw [← direct_link ]; exact branch_smooth h contDiffAt_fst rfl ((axesP G c).contDiff.contDiffAt.comp (f:=Prod.snd) 0 contDiffAt_snd) (map_zero _) t b
lemma thermal_zero (h:d.OK G)(b):consume d (G:=G) t b 0=0:= by
     unfold consume; simp [account_flat h]
lemma thermal_stat (h:d.OK G): Radial.Stationary (consume d t 1 (G:=G)):= Inherit.stable (thermal d t h 1) (thermal_zero d t h 1) (fun x=> action_nonneg ..)

-- probability tags at germ of conditional path ALL fine interior tree links. Since writing from `account`
-- not assuming another raw measure. Sector priors at germ equal. Re-exp not dependence on arbitrary D Tag choices.
lemma climate (h:d.OK G)(b:ℕ→ℝ)(t':d.Tags): consume d (G:=G) t b=ᶠ[𝓝 0] consume d t' b:= by
     unfold consume; simp_rw [← direct_link ]; exact branch_independent h contDiffAt_fst rfl t t' b
lemma likeliest (h:d.OK G): ∀ᶠ x : SpaceF G d in 𝓝 0, ∀ t:d.Tags,d.probability t (d.tablePath x.1)=(Fintype.card d.Tags:ℝ)⁻¹:= Filter.eventually_all.mpr fun t=> branch_uniform h (v:=Prod.fst) contDiffAt_fst rfl t

-- Core cost
local notation "Fv"=> SpaceF G d
def jointV : Quadratic (SpaceF G d):= Quadratic.genesis 1 ( H 1 ) -- before integrating
local notation "Υ"=> (jointV (G:=G) d t) -- maybe f param order? test
local notation "μ"=> tangent G d.Links

lemma progress (x:SpaceF G d): (Υ).flourish x/2= jet ( H 1 ) 2 x:= by rw [jointV,Quadratic.native]; rw [show term 1 0= (1:ℝ) from PowerSeries.coeff_zero_one]; ring
lemma core_life (h:d.OK G)(x: Descent.Coordinates G d): (Υ).core.flourish x=2*jet (phase G d t) 2 x:= by
     let L:= ContinuousLinearMap.inl ℝ (Coordinates G d) (Pins G c); have he : Descent.phase G d t= ( H 1 ) ∘ L:= funext fun x=> by change _=d.account 1 t (expLinks _ _ (0:Pins G c)) _; rw [ identity_zero ]; rfl
     rw [ he, GermLaplace.jet_pull L _ ((thermal d t h _).of_le le_top), ← progress ]; change (_:ℝ)= 2* (Quadratic.flourish (Quadratic.core Υ) x /2); ring

variable (hp:d.Room G)
include hp
lemma legacy : ( Quadratic.core Υ ).P= (ambient t hp).P:= by
     refine Quadratic.records ( Quadratic.core Υ ) ( Quadratic.recordQ (ambient t hp) ) (fun x=>?_); rw [core_life d t (room_ok d hp), Descent.half ]; change _= Descent.quadratic G d t x x; ring
lemma gives : (Quadratic.core Υ).RespectsPrice:= ⟨ ambient t hp,legacy d t hp⟩
local notation "δ"=> gives d t hp
lemma equivalent : Quadratic.RespectsPrice.inner (gives d t hp)= ambient t hp:= Quadratic.RespectsPrice.pinpoints _ ( legacy d t hp )

-- exposed full quotient static.Tags.This extension intentionally uses chosen `t` germ equivalent.
def retained (d:Descent n c)(t:d.Tags)(hp:d.Room G): Quadratic (Pins G c):= Quadratic.reduced (jointV d t) (gives d t hp)

section step
omit hp
variable (S:StepData c f)(T:Forest S.ratio)(d:Descent n f)(t:d.Tags)(b:S.Choices)
local notation "D"=> Descent.push S T d
local notation "η"=> ( show (Descent.push S T d).Tags from (b,t))
abbrev Future (G:Gauge)(S:StepData c f)(T:Forest S.ratio):= Direction G T.Free
local notation "Fr"=> Future G S T
local notation "N"=> SpaceF G ( Descent.push S T d )
local notation "Kc"=> Pins G c
abbrev combine (x: T.Free → G.El): Pins G f := fun i=> G.plog (G.mat (T.drape x i)) -- not used

def pext (G:Gauge)(S:StepData c f)(T:Forest S.ratio): Future G S T→ₗ[ℝ] Pins G f := LinearMap.pi fun i=> if h:i∈ T.trunks then 0 else LinearMap.proj (Subtype.mk i h : T.Free)
def gate (G:Gauge)(S:StepData c f)(T:Forest S.ratio): (Future G S T × Pins G c)→ₗ[ℝ] Pins G f:= pext G S T ∘ₗ LinearMap.fst ..
lemma inserts (x:Future G S T) : expLinks G _ (pext G S T x)=T.drape ( expLinks G T.Free x ):= by
   ext1 i; by_cases h:i∈ T.trunks; · simp only [expLinks,pext,LinearMap.pi_apply, dif_pos h]; exact G.mat_lieExp_zero.trans ((T.on_tree _ (⟨i,h⟩:_)).symm)
   simp only [expLinks,pext,LinearMap.pi_apply,dif_neg h]; exact (T.off_tree ( expLinks G T.Free x ) (⟨i,h⟩:_)).symm

def tax (S:StepData c f)(T:Forest S.ratio)(b:S.Choices) : Future G S T × Pins G c→ℝ:= fun x=> tagEnergy S b ( T.drape (expLinks G T.Free x.1) ) (expLinks G _ x.2)
local notation "E"=> Coordinates G d
-- re-index fast all. This includes the canonical order (prior history, THEN current fine).
def fusion (G:Gauge)(S:StepData c f)(T:Forest S.ratio)(d:Descent n f) : ((Coordinates G d) × Future G S T)≃ₗ[ℝ] Coordinates G ( Descent.push S T d ):= (LinearEquiv.prodComm ℝ (Coordinates G d) (Future G S T)).trans (LinearEquiv.sumPiEquivProdPi ℝ T.Free d.Links (fun _=> G.Color)).symm -- type lookup
local notation "π"=> (CityHistory.fusion G S T d)
def partΧ (G:Gauge)(S:StepData c f)(T:Forest S.ratio)(d:Descent n f) : (SpaceF G ( Descent.push S T d ))→ₗ[ℝ] SpaceF G d:= toward (gate G S T) ∘ₗ ( expandGauge (CityHistory.fusion G S T d) ).symm.toLinearMap

def partΥ (G:Gauge)(S:StepData c f)(T:Forest S.ratio)(d:Descent n f) : (SpaceF G (Descent.push S T d))→ₗ[ℝ] Future G S T × Pins G c:= (LinearMap.snd ..) ∘ₗ (expandGauge (CityHistory.fusion G S T d)).symm.toLinearMap
lemma places (x:Coordinates G d)(p:Future G S T)(j:Pins G c) : expandGauge (π) (x,p,j)=(Sum.elim p x,j):= by refine Prod.ext ?_ rfl; change fusion G S T d (x,p) = Sum.elim p x; apply funext; intro i; change (Equiv.sumPiEquivProdPi (fun _ : T.Free ⊕ d.Links=> G.Color)).symm (p,x) i=(_); cases ih:i <;> rfl
lemma hx_part (x:E)(p:Fr)(j:Kc): partΧ G S T d (expandGauge (π) (x,p,j))=(x, pext G S T p):= by unfold partΧ; rw [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]; rfl
lemma hy_part (x:E)(p:Fr)(j:Kc): partΥ G S T d (expandGauge (π) (x,p,j))=(p,j):= by unfold partΥ; rw [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]; rfl

lemma at_step (β:ℕ→ℝ)(x:N) : consume (Descent.push S T d) η β x=consume d t (upβ β) (partΧ G S T d x)+β 1* tax S T b (partΥ G S T d x):= by
   obtain ⟨⟨x,⟨p,j⟩⟩,rfl⟩:= (expandGauge (π)).surjective x; rw [hx_part,hy_part, places ];
   change β 1 * tagEnergy S b _ _ + d.account (upβ β) t _ _= consume d t _ _+ _; unfold tax consume; rw [ inserts S T ]; exact add_comm ..
end step
end YM.FVA2.CityHistory
