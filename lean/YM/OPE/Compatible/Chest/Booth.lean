import YM.OPE.Compatible.Chest.Kru
import YM.OPE.Compatible.Tune.Theta
import YM.OPE.Compatible.Tune.Race
import YM.OPE.Compatible.Cant.Cadre
import YM.OPE.Compatible.Cant.Wiz
import YM.OPE.Compatible.Cant.View
import YM.OPE.Compatible.Cant.Nob
import YM.OPE.Compatible.Cant.Past
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Cant.Fat
/-!
# Readouts in the three phases

Under the `Stone` hypothesis, `light` chooses three families of continuous
linear maps whose sum after `StageM` gives the phase-two readout. Each family
has a uniform polynomial norm bound in `Y`. `Light.windy` and `Light.zenith`
compute the phase-one and phase-zero readouts by shifting the input.
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
local notation "JΛ"=> Fin (l+1) 
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
private abbrev phaseOperator (W : GlowPack Hp Z a (k := k)) (u : Phase) :=
  M → Terra G τ d u →L[ℝ] OrthoC W

private def phasePrice (W : GlowPack Hp Z a (k := k)) (u : Phase)
    (A : phaseOperator (M := M) W u) (price : M → ℝ) : Prop :=
  Wealth A price 1

private def threePhaseReadout
    (S : M → Terra G τ d 2 →L[ℝ] OrthoC W)
    (T : M → Terra G τ d 1 →L[ℝ] OrthoC W)
    (F : M → Terra G τ d 0 →L[ℝ] OrthoC W) (m : M) (v : solar G d τ) : Prop :=
  Eψ D m 2 v =
    S m (StageM (K := K) (e := l + 1) (fun i => (V i).gear) hp 2 m v) +
    T m (StageM (K := K) (e := l + 1) (fun i => (V i).gear) hp 1 m v) +
    F m (StageM (K := K) (e := l + 1) (fun i => (V i).gear) hp 0 m v)

set_option maxHeartbeats 200000 in
structure Light where
     S : phaseOperator (M := M) W 2
     T : phaseOperator (M := M) W 1
     F : phaseOperator (M := M) W 0
     sCost : phasePrice W 2 S Y
     tCost : phasePrice W 1 T Y
     fCost : phasePrice W 0 F Y
     Lup (m:M)(v:solar G d τ) : threePhaseReadout D S T F m v
set_option maxHeartbeats 200000 in
lemma light (h:Stone Z Y U): Nonempty (Light D):=by
       obtain ⟨S,T,Q,P,hV,H',h'⟩:= selection D h; exact ⟨S,T,Q,P,hV,H',fun m v=> DFunLike.congr_fun (congr_fun h' m) v⟩
-- One application of `trellisA` kills phase zero and lifts each lower phase.
section Op
variable (h:Aware d τ)(X':M→Train r)(hv:4≤r)(u:Phase)
variable [NormedAddCommGroup E][NormedSpace ℝ E]
noncomputable abbrev Dark (v:Train r): Terra G τ d u→L[ℝ] Terra G τ d u:= latent (e:=e) (K:=K) hv u v
lemma cookM (S: Terra G τ d 2→L[ℝ] E)(T:Terra G τ d 1→L[ℝ] E)(F: Terra G τ d 0→L[ℝ] E)(i:M)(p:solar G d τ):
        let q:=trellisA G h p; let f:= latent (K:=K) (d:=d) (τ:=τ) (e:=e) hv 1 (X' i); let t:=latent (K:=K) (d:=d) (τ:=τ) (e:=e) hv 2 (X' i)
        S (StageM (e:=e) (K:=K) X' hv 2 i q)+ T (StageM (e:=e) (K:=K) X' hv 1 i q)+ F (StageM (e:=e) (K:=K) X' hv 0 i q)= S (t (armP G h 1 2 (by decide) (p.val 1))) + T (f (armP G h 0 1 (by decide) (p.val 0))):=by
             intro q f t; let b:=latent (K:=K) (τ:=τ) (d:=d) (e:=e) hv 0 (X' i); rw [show StageM (e:=e) (K:=K) X' hv 0 i q=0 from (by change b (Candy G h p.val 0)=0; rw [pal h p.val 0 (by decide),map_zero]),map_zero,add_zero]; change S (t (q.val 2))+ T (f (q.val 1))=_; rw [show q.val 2= _ from glee h p.val 2 1 rfl,show q.val 1=_ from glee h p.val 1 0 rfl]
lemma cukeM (S: Terra G τ d 2→L[ℝ] E)(T:Terra G τ d 1→L[ℝ] E)(i:M)(p:solar G d τ):
        let q:=trellisA G h p; let f:= latent (K:=K) (d:=d) (τ:=τ) (e:=e) hv 1 (X' i); let t:=latent (K:=K) (d:=d) (τ:=τ) (e:=e) hv 2 (X' i)
        S (t (armP G h 1 2 (by decide) (q.val 1))) + T (f (armP G h 0 1 (by decide) (q.val 0)))= S (t (armP G h 1 2 (by decide) (armP G h 0 1 (by decide) (p.val 0)))):=by intro q f t; rw[show q.val 1=_ from glee h p.val 1 0 rfl,show q.val 0=0 from pal h p.val 0 (by decide),map_zero,map_zero,map_zero,add_zero]
end Op
namespace Light
variable {D} (T:Light D)(i':M)
local notation "g"=> Gift G D₀.aware
local notation "V'!"=> solar G d τ
noncomputable abbrev LatQ (m:M)(z:Phase): Terra G τ d z→L[ℝ] Terra G τ d z:= latent (K:=K) (e:=l+1) hp z (V m).gear
include T

set_option maxHeartbeats 200000 in
lemma windy (m:M)(p:solar G d τ):
     let f:= latent (K:=K) (τ:=τ) (d:=d) (e:=l+1) hp 1 (V m).gear; let S:= latent (K:=K) (τ:=τ) (d:=d) (e:=l+1) hp 2 (V m).gear;
     Eψ D m 1 p=T.S m (S (armP G D₀.aware 1 2 (by decide) (p.val 1))) + T.T m (f (armP G D₀.aware 0 1 (by decide) (p.val 0))):=by
        intro f t; exact (shifts D m 1 2 rfl p).symm.trans ((T.Lup m (trellisA G D₀.aware p)).trans (cookM (K:=K) D₀.aware (fun i=> (V i).gear) hp (e:=l+1) (T.S m) (T.T m) (T.F m) m p))
set_option maxHeartbeats 200000 in
lemma zenith (m:M)(p:solar G d τ):
     let S:=latent (K:=K) (τ:=τ) (d:=d) (e:=l+1) hp 2 (V m).gear
     Eψ D m 0 p=T.S m (S (armP G D₀.aware 1 2 (by decide) (armP G D₀.aware 0 1 (by decide) (p.val 0)))):=by
        intro f; exact (shifts D m 0 1 rfl p).symm.trans ((windy T m (trellisA G D₀.aware p)).trans (cukeM (K:=K) D₀.aware (fun i=> (V i).gear) hp (e:=l+1) (T.S m) (T.T m) m p))
end Light
end
end YM.OPE.Stroke
