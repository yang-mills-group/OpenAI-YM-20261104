import YM.OPE.Compatible.Cres.Away
import YM.OPE.Compatible.Ice.Sneer
/-!
# Comparing readings after transport and a change of parameter

`Fickle` compares the target reading at `Ω` with the scaled, transported source
reading at `W'`. It uses eventual agreement of the translated fields, the `Audible`
bound at exponent `y`, and the bound on `Ω - W'`. With `3 * u ≤ y < t'` and the
stated field and frame estimates, the difference has rate exponent `t'`.
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

section Third
open GlowPack Silt.Phere Ibis
variable (f:I→M) (g:I→Q){L:Filter I} {Xη W' α γ δ ξ:I→ℝ}
variable {Vη:Q→ℝ}{DΦ:(k:Q)→Alps K T j (Vη k)}{V':Z.Ω Q Vη}{hp':4 ≤ j}{hz: 1≤Vη}
variable (D':Cart Hp Z a W V' hz hp' DΦ)

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 256000
local notation "ρt"=> LineCt W
variable (P0:I→solar G d τ) (S:I→Tracts G d τ→L[ℝ] Tracts G d τ)
variable (t_:Q)
variable (hs' : ∀ᶠ i in L,Ace D₀ H hs a (V (f i)) (DΦ (g i)) (zero_le_one.trans (hq _)) (zero_le_one.trans (hz _)) hp hp' r (S i)) (hV:Tendsto Xη L atTop)
variable (hf:RateLE L Xη (fun i=>Y (f i)) 0)(hQ:RateLE L Xη (fun i=>Vη (g i)) 0)(ht:RateLE L Xη S 0)(hk: RateLE L Xη W' u)(hU:u≤0)

variable (B0:I→solar G d τ)(R0:I→solar G d τ)
variable {N:I→Side} (x:∀ i, Site (N i)) {β δ:I→ℝ}
local notation "K!"=> solar G d τ
local notation "ℓ!"=> Vη
variable (ha:Alive L Xη R0)(hC: Alive L Xη B0)(hα:RateLE L Xη α 0)(hB:RateLE L Xη β 0)
variable (y t':ℝ)(hz':y<t')(he:l+6 ≤ e)(hb: 3*u ≤y)
variable (hÄ: Stone Z Vη V')
variable (hw:∀ᶠ i in L,(Ibis.Hear (I:=I) (K:=K.K) (v:=u) G hp' τ d D₀.aware hz' (show l+1+6 ≤ e+1 from by omega) hU hb).choose (Xη i) ≤ (N i).val)
-- The translated comparison field agrees eventually with the transported source field.
variable (hT:∀ᶠ v in L, vintage G D₀.aware (-β v) (R0 v)= Emote (D₀:=D₀) (hp':=hp') (hp:=hp) (V:=V) (DΦ:=DΦ) (f v) (g v) (S v) (P0 v))
variable (hΦ: Ibis.Audible G K.K N L Xη j e (fun i=> (DΦ (g i)).gear) hp' (fun i:I=> Aview (vintage G D₀.aware (β i) (B0 i)- α i • R0 i) (x i) (W' i)) y)
variable {Ω:I→ℝ}(hΨ: RateLE L Xη Ω 0)(hD: RateLE L Xη (fun i=> Ω i-W' i) t')
include hs' hV hf ht hU hQ ha hC hα hB hz' he hb hÄ hw hΦ hk hΨ hD hT
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
lemma Fickle (hv:RateLE L Xη P0 0) : RateLE L Xη (fun i=> τPledge D' (g i) (Ω i) (B0 i) - α i • (τΡ D (f i) D' (g i) (S i) (W' i) (τPledge D (f i) (W' i) (P0 i)))) t':=by
        let Cπ(v):= vintage G D₀.aware (β v) (B0 v)- α v • R0 v; have hc: Alive L Xη Cπ:= (hC.γΖ hV hB D₀.aware).minus (ha.bend hα) hV
        have hpz:= Paying D' hÄ y t' hz' he hU hb _ rfl L Xη W' Cπ N x g hV hw hc hk hQ hΦ _ hB.neg; have he':= ζLeap D' g hV hQ B0 (hC.score hV) hk hU hΨ hD; have hx :=Vision D f g D' P0 S hs' hV hf hQ ht hk hU hv
        refine (((he'.add hpz hV).add ((hα.smul hx).mono (by linarith only [hz',hb])) hV)).congr ?_; filter_upwards [hT] with i hi;
        let v:= B0 i; let x:= R0 i; let t:= Emote (D₀:=D₀) (hp':=hp') (hp:=hp) (V:=V) (DΦ:=DΦ) (f i) (g i) (S i) (P0 i); let y:= α i; let H:= τPledge D' (g i) (W' i); let F:= vintage G D₀.aware (-β i); let q:=vintage G D₀.aware (β i) v
        have hp:F q=v:=congr_arg F (congr_arg (fun b=>vintage G D₀.aware b v) (neg_neg (β i)).symm)|>.trans (Ibis.undo G D₀.aware (-β i) v); let a:= τΡ D (f i) D' (g i) (S i) (W' i) (τPledge D (f i) (W' i) (P0 i)); exact swiftR H F v q x t y (τPledge D' (g i) (Ω i) v) a hi hp
where swiftR {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y] (H:X→L[ℝ] Y)(F:X→L[ℝ] X)(v q x t:X)(y:ℝ)(p a:Y)(h:F x=t)(hv:F q=v): p-H v+ H (F (q-y • x))+ y • (H t-a)=p-y • a:=by
           rw [map_sub F, map_smul F, H.map_sub, H.map_smul,h,hv,smul_sub]; abel
end Third
end
end YM.OPE.Stroke
