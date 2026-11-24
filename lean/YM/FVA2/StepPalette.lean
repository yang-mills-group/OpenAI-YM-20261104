import YM.FVA2.Harvest
import YM.FVA2.Interface
/-!
# Every step on the *inversion* branch's actual Fk.read realization

At steps beyond top, inherits formal unmarked quadratic U.Q and interaction U.W. Include the
ENTIRE bare step penalty with that same S t and leading cost of `w β` in Fk ray action. The
remaining order/ticket ledger is a multiplication/re-expression as formal interactions, exactly
calculated with `Fk.read` by the Cart rule. No Taylor-series convergence assumption or actual
mask. Then characterize BOTH the Ledger income = next step unmarked density W and, computed
WITH IT, all marked outputs. Use `Harvest.income_all` if needing to keep proportions incl Hessian.
Steady is **not** a requirement as we're just identifying the coefficient prescriptions here (not
using any envelopes). Can't use this file as if showing an estimate for any actual model.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.Perch
open Filter Topology Function PowerSeries Finset MeasureTheory Lattice Gauge RG
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice
open FormalOPE.RG10.MultiGauge.Blocking FormalOPE.RG10.MarkovChain.Warp
open FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.OpenSlots FormalOPE.RG10.Sync
open FormalOPE.RG10.BlockGauge FormalOPE.RG10.BlockGauge.Fabric FormalOPE.RG10.Inherit
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Precision
open GaussianScore RGComparison.Core16 RGComparison.Core16.Therm RGComparison.Core16.Lumen
open RayScatter RayScatter.Harvest OrbitPlanet
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {c f n:Side}{S:StepData c f} 

section Z
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
lemma analyticQ (P:Quadratic E): ContDiff ℝ ω (fun x=>P.flourish x /2):= ((( LinearMap.toContinuousLinearMap (E:=E) (F':=ℝ) ).toLinearMap.comp P.P ).toContinuousLinearMap.contDiff.clm_apply contDiff_id).div_const _
lemma chargeQ (P:Quadratic E)(x:E): jet (fun x=>P.flourish x/2) 2 x=P.flourish x/2:= by
    let L:=fun x:E=>P.flourish x/2; have he(t:ℝ): L (t • x)= t^2*L x := by unfold L Quadratic.flourish; rw [map_smul,map_smul]; simp; ring
    rw [ homogeneous_derivative L x 2 (( analyticQ P|>.contDiffAt ).of_le le_top),funext he, iteratedDeriv_mul_const_field,iteratedDeriv_fun_pow_zero]; norm_num [Nat.factorial]; ring
end Z

variable (P:Inside S.ratio)(t:S.Choices)(h:S.patch.Branches S.kernel G)(U:Unmasked G f)
local notation "L"=> Blocking.Index S P
local notation "EΩ"=> OrbitPlanet.Joint (G:=G) P -- shadow Sigma
local notation "Q"=> Cross (G:=G) S P
local notation "W"=> Flats G c
local notation "ρ"=> OpenSlots.extend (G:=G) P
local notation "F"=> firstBill (G:=G) (n:=f)
local notation "K"=> Option (Orb.OEdge c)
variable (w: PowerSeries ℝ)

def stepprice : OrbitPlanet.Joint (G:=G) P →ℝ := fun x=> U.Q.flourish (blankRight P x) / 2 + term w 0 * substep P t x
lemma expands : stepprice P t U w =(fun x=> U.Q.flourish x /2 ) ∘ (blankRight P (G:=G)).toContinuousLinearMap + term w 0 • substep P t := rfl -- order of w using earlier variables

include h
lemma germ : ContDiffAt ℝ ω (stepprice P t U w) 0:= by rw [expands]; exact ContDiffAt.add (((( analyticQ .. ).comp ((blankRight P (G:=G)).toContinuousLinearMap.contDiff)).contDiffAt)) ((subReady P t h).const_smul (term w 0))
local notation "Δw"=> gated P U t w
lemma hasQ (x:OrbitPlanet.Joint (G:=G) P): (Δw).flourish x=2*jet (stepprice P t U w) 2 x := by
    let Lθ:= (blankRight P (G:=G)).toContinuousLinearMap
    let J(v):=U.Q.flourish v/2; let y:=term w 0
    rw [expands, Inherit.plus (a:=J ∘ Lθ) (b:=y • substep P t) (2:ℕ) (((analyticQ _).comp Lθ.contDiff).contDiffAt) ((subReady P t h).const_smul y) x, Inherit.times _ y (subReady P t h), GermLaplace.jet_pull Lθ _ ( ContDiffAt.of_le (analyticQ _).contDiffAt le_top ), chargeQ ]; change U.Q.flourish (Lθ x)+ ( Quadratic.genesis w (substep P t) ).flourish x=_; rw [Quadratic.native]; change _+2*(y * _) = _; unfold Lθ y; ring -- try
omit h

variable (Z:ChartRatio G)(hZ:LocalRatio Z)(hp:( Quadratic.core (gated P U t w)).RespectsPrice)(H:incline U.W)(y:Flats G c)

-- explicit Fk shelf.One analytic representative of heat for all costs.Fiber.L.No asp
local notation "yL"=> Forge.Sky G (Blocking.Index S P)
def lift_price (g:Forge.Sky G (Blocking.Index S P)):= U.Q.flourish (ρ (Inherit.down g))/2
def weather (j: Option (Orb.OEdge c)) (x:Lumen.Point G (Blocking.Index S P)) := let g:=fun i=> launch ( x.2 i ); j.elim (lift_price P U g) (fun e=> term w 0 * plank t (drape P g) e x.1)
def slot : Shelf G (Option (Orb.OEdge c)) (Blocking.Index S P) := { OrbitPlanet.code P t (G:=G) with «U»:= weather P t U w }

def phase (y:Flats G c): Planet (slot P t U w) f (Blocking.Index S P) (Option (Orb.OEdge c)) Unit := {
 loc := (OrbitPlanet.frame P t y).loc
 root := (OrbitPlanet.frame P t y).root
 cost a _ v j:= j.elim (lift_price P U v) (fun e=> term w 0 * plank t (drape P v) e (a • y e))
 meter := (OrbitPlanet.frame P t y).meter
 glyph := id
 stem := (OrbitPlanet.frame P t y).stem
 ray := ( OrbitPlanet.frame P t y ).ray }
local notation "eY"=> phase P t U w y
lemma bureau (g:ℝ)(x:yL): (eY).bureau g x= Real.exp (-(U.Q.flourish (ρ ( Inherit.down x))/2 + term w 0 * BlockGauge.penalty S t (drape P x) ( expLinks G _ (g • y)) ) / g^2 ) := by
    unfold Planet.bureau Forge.Base.output; rw [Fintype.sum_unique]; change 1 * Real.exp (- ((eY).F g|>.action () x) / g^2)= _; rw [one_mul]; refine congr_arg _ (congr_arg (fun x:ℝ=> -x/g^2) ?_); unfold Forge.Base.action; rw [Fintype.sum_option]; apply congr_arg₂ _ rfl (?_); rw [← earned t (drape P x) (g • y), Finset.mul_sum ]; rfl

lemma arise : Fk.rise eY=ᶠ[𝓝 0] charge (stepprice P t U w) 1 y:= by
    filter_upwards [ (continuous_snd.tendsto (0:Fk.Door G (Blocking.Index S P))).eventually Inherit.down_left, launched (G:=G) (P:=P) ] with x hx hq
    let g:= Fk.spread x.2; let E:EΩ:= RayScatter.recover y x -- annotation syntax
    have he : ( fun i=> launch ( G.curvature (g i) ))=g:= funext hq
    have ht (k:K) : Fk.postage eY x k = (eY).cost x.1 () g k:= by cases k with|none=> exact congr_arg (lift_price P U) he | some i=> exact congr_arg (fun g=> term w 0 * plank t (drape P g) _ ( x.1 • y i )) he
    rw [Fk.rise,Fk.lapse, show (∑ i:Option (Orb.OEdge c),Fk.postage eY x i)=_ from Finset.sum_congr rfl (fun i _=> ht i), Fintype.sum_option ]; change _+ (lift_price P U g+ ∑ i, term w 0 * plank t (drape P g) i _) = 1*x.1^2+ stepprice P t U w E; rw [ one_mul,← Finset.mul_sum,lift_price,show Inherit.down g=x.2 from hx, show (∑ i,plank t (drape P g) i (x.1 • y i))= _ from earned t (drape P g) (x.1 • y) ]; unfold g; rw [draped]; rfl

local notation "uκ"=> Fork.interaction Z (stepprice P t U w)
local notation "U'"=> receipt P t Z w U
local notation "ν"=> tangent G (Blocking.Index S P)
local notation "H'"=> ( Fork.inclineI (p:=stepprice P t U w) Z hZ )
def reco (r:Ticket (OrbitPlanet.Joint (G:=G) P)): PowerSeries ℝ:= page (phase P t U w y) Z y (Harvest.shift Z (U'* r) (p:=stepprice P t U w))
include h hZ hp
lemma reconstruct (r:Ticket (OrbitPlanet.Joint (G:=G) P)) : PowerSeries.mk (Fk.birth eY Z) * reco P t U w Z y r= C ( basePower Δw hp y ν 1 * Stack.overhead Z L ) * Stack.read y ((Δw).uptake ν hp ( U' * r ) ):= income_all eY Z hZ (germ P t h U w) Δw (hasQ P t h U w) hp y (arise ..) _
lemma revenue : PowerSeries.mk (Fk.birth eY Z) * reco P t U w Z y 1= C ( basePower Δw hp y ν 1 * Stack.overhead Z L ) * Stack.read y (Update P t Z w U hp).W := by rw [reconstruct P t h U w Z hZ hp,mul_one]; rfl
include H
lemma source_all (r:Ticket (OrbitPlanet.Joint (G:=G) P)) : Stack.read y (Broadcast P t Z w U hp r)=reco P t U w Z y r * (reco P t U w Z y 1)⁻¹:= by
    unfold reco; rw [mul_one]; exact full_order eY Z hZ (germ P t h U w) Δw (hasQ P t h U w) hp y (arise ..) _ (along hZ w H) r
lemma beginning : constantCoeff (reco P t U w Z y 1)=1:= by
    unfold reco; rw [mul_one]; exact page_up eY Z hZ (germ P t h U w) Δw (hasQ P t h U w) hp y (arise ..) _ (along hZ w H)

-- pull basis normalization to standard Proof. Tour.Spec.Unique incomes cancel
lemma primary : 0< Fk.birth eY Z 0:= RayScatter.Fork.positive eY Z hZ (germ P t h U w) Δw (hasQ P t h U w) hp y (arise P t U w y)

lemma incomeQ : constantCoeff (Stack.read y (Update P t Z w U hp).W)=1:= by rw [← coeff_zero_eq_constantCoeff_apply, Stack.reading_term, coeff_zero_eq_constantCoeff_apply, funded hZ _ H]; rfl
omit h hp hZ H

structure TrueStep (P:Inside S.ratio)(t:S.Choices)(U:Unmasked G f)(w:PowerSeries ℝ)(Z:ChartRatio G)(hp:(Quadratic.core (gated P U t w)).RespectsPrice):Prop where
    tow : Open.floatD (P:=P) Z w hp
    pure (y:Flats G c) : 0< Fk.birth (phase P t U w y) Z 0
    flow (y:Flats G c) : constantCoeff (reco P t U w Z y 1)=1
    normal (y:Flats G c) : PowerSeries.mk (Fk.birth (phase P t U w y) Z) * reco P t U w Z y 1= C ( basePower (gated P U t w) hp y (tangent G (Blocking.Index S P)) 1 * Stack.overhead Z (Blocking.Index S P) ) * Stack.read y (Update P t Z w U hp).W
    budget (y:Flats G c)(r:Ticket (OrbitPlanet.Joint (G:=G) P)): Stack.read y (Broadcast P t Z w U hp r)=reco P t U w Z y r * (reco P t U w Z y 1)⁻¹

include h hZ hp H in
lemma fromEach : TrueStep P t U w Z hp:= ⟨ Open.transmits _ hZ hp H,primary P t h U w Z hZ hp H, beginning P t h U w Z hZ hp H,revenue P t h U w Z hZ hp , source_all P t h U w Z hZ hp H ⟩


def Each {n:Side}{Fp:Fabric G n} (T:Cloth Fp)(Wv:Unmasked G n)(a:Fp.Cost→PowerSeries ℝ)(h:Commission Z T Wv a): Prop := incline Wv.W ∧ match T with
 | .floor _ _ _=> True
 | .inLayer (t:=p) P T=> TrueStep P p Wv (a none) Z (Exists.choose h) ∧ Each T (Update P p Z (a none) Wv (Exists.choose h)) (a∘some) (Exists.choose_spec h)

include hZ
lemma bake {n: Side}{Fp:Fabric G n}(T:Cloth Fp) (V:Unmasked G n)(b:Fp.Cost→PowerSeries ℝ)(a:Commission Z T V b)(H:incline V.W): Each Z T V b a:= by
    cases T with
    | floor => exact ⟨ H,trivial ⟩
    | @inLayer c f S hΘ p h L' P C => rw [Each]; exact ⟨ H, fromEach P p hΘ V _ Z hZ _ H, bake C _ _ _ (funded hZ _ H _)⟩
termination_by structural T
omit hZ
lemma promises (F0:IteratedWilsonPrescription G n): Each F0.ratio F0.goods (initialFull G n ( F0.z none )) (F0.z ∘ some) ( Open.protocol F0 ):= bake F0.ratio F0.calibrated _ _ _ _ (OpenSlots.restores _ _)
end YM.FVA2.Perch
