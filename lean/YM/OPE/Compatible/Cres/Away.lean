import YM.OPE.Compatible.Cres.Adorn
/-!
# Transport of a quadratic reading between frames

`Eyes` identifies the reading after a change of frame, and `YearArc` shows that the
frame map commutes with `FlowP`. Under eventual `Ace` compatibility and the stated
rate bounds, `Vision` bounds the difference between the two transported `τPledge`
readings at exponent `3 * u`, where the parameter has exponent `u ≤ 0`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {Y:M→ℝ}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "JΛ"=> Fin (l+1) -- use
open Pipes
local notation "μ"=>lapPrice (Patch.L P)
section
open GlowPack
variable (W:GlowPack Hp Z a (k:=k)) (U:Z.Ω M Y)(hq:1 ≤ Y)(hp:4 ≤ i)(V:(i':M)→Alps K T i (Y i'))
local notation "W!"=>Dux G l W.W
local notation "E!"=>Eagle Hp Z a W
variable {W Hp Z a U V} {hq hp}
variable (D:Cart Hp Z a W U hq hp V) (j':M)
open GlowPack
open Silt.Phere
-- Source and target readings use their respective frames.
section Third
open GlowPack Silt.Phere Ibis
variable (f:I→M) (g:I→Q){L:Filter I} {Xη W' α γ δ ξ:I→ℝ}
variable {Vη:Q→ℝ}{DΦ:(k:Q)→Alps K T j (Vη k)}{V':Z.Ω Q Vη}{hp':4 ≤ j}{hz: 1≤Vη}
variable (D':Cart Hp Z a W V' hz hp' DΦ)
-- The shift acts on the field before the target frame reads it.
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
local notation "ρt"=> LineCt W
variable (P0:I→solar G d τ) (S:I→Tracts G d τ→L[ℝ] Tracts G d τ)
variable (t_:Q)
variable (U₀:Tracts G d τ→L[ℝ] Tracts G d τ)
variable (Xo:Ace D₀ H hs a (V j') (DΦ t_) (zero_le_one.trans (hq j')) (zero_le_one.trans (hz t_)) hp hp' r U₀)
local notation "κΠ"=> EFrame D j' D' t_ U₀
private lemma reframeRead {A B C : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    (before after : A ≃L[ℝ] B) (read next : A →L[ℝ] C)
    (shift : A →L[ℝ] A) (frame : C →L[ℝ] C)
    (wire : ∀ y, next (shift y) = frame (read y)) (x : B) :
    (next.comp after.symm.toContinuousLinearMap) (after (shift (before.symm x))) =
      frame ((read.comp before.symm.toContinuousLinearMap) x) := by
  change next (after.symm (after (shift (before.symm x)))) = frame (read (before.symm x))
  rw [after.symm_apply_apply]
  exact wire _

private lemma framePrice {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (first : I → B →L[ℝ] A) (shift : I → A →L[ℝ] A) (last : I → A →L[ℝ] B)
    (hfirst : RateLE L Xη first 0) (hshift : RateLE L Xη shift 0)
    (hlast : RateLE L Xη last 0) :
    RateLE L Xη (fun i => (last i).comp ((shift i).comp (first i))) 0 := by
  apply RateLE.of_norm_le ((hlast.norm.mul (hshift.norm.mul hfirst.norm)).mono (by simp))
  apply Eventually.of_forall
  intro i
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))

include Xo
lemma Eyes (x:solar G d τ): Eout D' t_ (Fallix G D₀.aware K (DΦ t_).gear hp' (U₀ ((Fallix G D₀.aware K (V j').gear hp).symm x)))= (EFrame D j' D' t_ U₀) (Eout D j' x):=by
  exact reframeRead (Fallix G D₀.aware K (V j').gear hp)
    (Fallix G D₀.aware K (DΦ t_).gear hp') (FirP D j') (FirP D' t_) U₀
    (EFrame D j' D' t_ U₀) (starWire D j' D' t_ U₀ Xo) x
lemma YearArc (x: LineCt W): EFrame D j' D' t_ U₀ (FlowP (Eagle Hp Z a W) x)= FlowP (Eagle Hp Z a W) ((EFrame D j' D' t_ U₀) x) := (rayT D j' D' t_ U₀ Xo).trips x
omit Xo
noncomputable abbrev μvort : Tracts G d τ→L[ℝ] LineCt W:= FirP D j' 
set_option quotPrecheck false
local notation "FW"=> fun i=>EFrame D (f i) D' (g i) (S i)
-- Compatibility is needed eventually along the chosen filter.
variable (hs' : ∀ᶠ i in L,Ace D₀ H hs a (V (f i)) (DΦ (g i)) (zero_le_one.trans (hq _)) (zero_le_one.trans (hz _)) hp hp' r (S i)) (hV:Tendsto Xη L atTop)

variable (hf:RateLE L Xη (fun i=>Y (f i)) 0)(hQ:RateLE L Xη (fun i=>Vη (g i)) 0)(ht:RateLE L Xη S 0)(hk: RateLE L Xη W' u)(hU:u≤0)
include hV hf hQ ht
-- Composing the two frame maps with the shift gives rate exponent zero.
lemma Uclock: RateLE L Xη (FW) 0:=by
  exact framePrice (fun i => Pel D (f i)) S (fun i => FirP D' (g i))
    (height_W L Xη (fun i => Pel D i) f (PelCost D) hV hf) ht
    (height_W L Xη (fun i => FirP D' i) g (pricedA' Hp Z a W _ hz hp' DΦ D') hV hQ)
include hs' hU hk
noncomputable abbrev τΡ (q:Tracts G d τ→L[ℝ] Tracts G d τ)(w:ℝ): OrthoC W→L[ℝ] OrthoC W:= (border w (EFrame D j' D' t_ q).toLinearMap).toContinuousLinearMap
noncomputable abbrev Emote (x:solar G d τ): solar G d τ:= Fallix G D₀.aware K (DΦ t_).gear hp' (U₀ ((Fallix G D₀.aware K (V j').gear hp).symm x))
lemma Vision (hW:RateLE L Xη P0 0): RateLE L Xη (fun i=> τPledge D' (g i) (W' i) (Emote (D₀:=D₀) (hp':=hp') (hp:=hp) (V:=V) (DΦ:=DΦ) (f i) (g i) (S i) (P0 i))-τΡ D (f i) D' (g i) (S i) (W' i) (τPledge D (f i) (W' i) (P0 i))) (3*u):=by
        let F:=FW; let Y(i):= Eout D (f i) (P0 i); have he :∀ᶠ i in L,∀ x:Mel E!,F i (FlowP (Eagle Hp Z a W) x)=FlowP (Eagle Hp Z a W) (F i x):= hs'.mono fun i hx=> YearArc D (f i) D' (g i) (S i) hx; have hx:= φPole F Y hV (ΓForm D f hV hf P0 hW) (Uclock D f g D' S hV hf hQ ht) he hk hU; apply hx.congr; filter_upwards [hs'] with i hi; 
        exact congr_arg (fun y:LineCt W=> FilmP (Eagle Hp Z a W) (W' i) y - (τΡ D (f i) D' (g i) (S i) (W' i)) (τPledge D (f i) (W' i) (P0 i))) (Eyes D (f i) D' (g i) (S i) hi (P0 i)|>.symm)
end Third
end
end YM.OPE.Stroke
