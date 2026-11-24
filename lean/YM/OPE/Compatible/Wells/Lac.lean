import YM.OPE.Compatible.Wells.Prance
import YM.OPE.Compatible.Swoon.Oort
/-!
# Genuine chamber innovation charges. Formal Haar characters.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset Tensor
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance StepsL Claw Prom Coin
variable {i j d k m r l b:ℕ}{n:Side}
variable (hp:Board n (r+1))
variable {P:ChartRatio G} (hr:LocalRatio P)(u:G.Color)
-- draw registers
section
variable {I:Type}[Fintype I]
open Metric
include hr
lemma jacRank (x:Libra.Keys G I):
       let Y:= Chart.jacobian P (U:=I); let t:= Y 0
       0<t ∧ Pawn.mold Y 0 x=plainJ t * (flareTok 0 (jet (Zeph.feeX P) 2 x)):=by
          let v:= looper P (I:=I); let c:= jackpot P I; let p:= v + fun _=> c; let L:= Real.exp ∘ p; intro Y t; have ht:Y=ᶠ[𝓝 0] L:=parW P hr; have hh: Y 0=L 0:=ht.eq_of_nhds; obtain ⟨hx,hQ⟩:= pals (I:=I) P hr; have he:ContDiffAt ℝ ω p 0:=hx.add contDiffAt_const; have hs:fderiv ℝ p 0=0:=by unfold p; rw[fderiv_add (hx.differentiableAt (by simp)) (differentiableAt_const _), show fderiv ℝ v 0 = 0 from hQ,fderiv_const_apply,add_zero] -- syntax hx
          have hg:jet L 2 x=t*jet v 2 x:=by rw [jetExp2 p x he hs, ← show t = Real.exp (p 0) from hh]; congr 1; rw [njet,njet, iteratedFDeriv_add_apply (f:=v) (hx.of_le le_top) contDiffAt_const, iteratedFDeriv_const_of_ne (by decide), Pi.zero_apply,add_zero] -- lhs p unfolds?
          have hz: jet L 1 x=0:=by unfold jet L; rw[iteratedFDeriv_one_apply,fderiv_comp _ Real.differentiableAt_exp (he.differentiableAt (by simp)),hs];simp
          refine ⟨Real.exp_pos (p 0)|>.trans_eq hh.symm,?_⟩; rw[meltSame _ _ ht]; apply JetS.eta
          · change jet L 0 x=t*1; rw [jet_zero,← hh,mul_one]
          · change jet L 1 x=t*0+0*1; rw[hz];ring
          change jet L 2 x=t*(jet (Zeph.feeX P) 2 x+0^2/2)+0*0+0*1; rw [hg,show v= _ from (show v=Zeph.feeX P from rfl)];ring
end
-- divergence identities translated
variable (x:Bid.Dir G n) (q:↥(fieldP r))
local notation "T!"=> Chamber G r
local notation "K!"=>turn (sailT G hp) x
abbrev R_τ (x:Bid.Dir G n) (p: Chamber G r):= turn (ContinuousLinearMap.id ℝ (Chamber G r)) (PinT G x) p
private lemma mountedAt (basis:Module.Basis G.ColorIndex ℝ G.Color) {I:Type}[Fintype I](p:I)(v:G.ColorIndex):
    Pawn.mold (tou p basis false u v) 0 = Pawn.mold (basis.coord v ∘ Cast false u) 0 ∘
      (ContinuousLinearMap.proj p : Keys G I →L[ℝ] G.Color):=by
  let f := basis.coord v ∘ Cast false u
  have smooth:ContDiffAt ℝ ω f 0:=
    (basis.coord v).toContinuousLinearMap.contDiff.contDiffAt.comp _ (cast_sm ..)
  exact moldC (ContinuousLinearMap.proj p : Keys G I →L[ℝ] G.Color) f smooth 0

private lemma shiftedRead (y:T!):
    (turn (sailT G hp) x y) (sett n 0 q.val) = (R_τ x y) q:=by
  rw [show sett n 0 q.val=terr hp q from ark_sett ..]
  change x (terr hp q) + sailT G hp y (terr hp q) = PinT G x q + y q
  rw [tide,PinS]

lemma mounts (v:G.ColorIndex): Mount (sett n 0 q.val) u false v ∘ turn (sailT G hp) x = Mount q u false v ∘ R_τ x:=by
  unfold Mount
  rw [mountedAt u (Phone G) (sett n 0 q.val) v,mountedAt u (Phone G) q v]
  funext y
  exact congrArg (Pawn.mold ((Phone G).coord v ∘ Cast false u) 0) (shiftedRead hp x q y)
include hp hr
lemma τPit :
       let Y (i:G.ColorIndex):= Mount (sett n 0 q.val) u false i ∘ turn (sailT G hp) x
       let j:= (Pawn.mold (Chart.jacobian P (U:=↥(fieldP r))) 0) ∘ R_τ x
       divergence (An q (Phone G)) Y univ*j+Flux (An q (Phone G)) Y univ j=0:=by
        intro Y j; let v:= Mount q u false; let g:=Pawn.mold (Chart.jacobian P (U:=↥(fieldP r))) 0; let p:= PinT (r:=r) G x; let f:= An q (Phone G); let Q:= ContinuousLinearMap.id ℝ T!; have hy: Y=(fun i=> v i ∘ turn Q p):= funext (mounts hp u x q); rw [hy, show j=g∘ turn Q p from rfl, turnZ Q p f v univ g (tallJ _ _),turnD Q p f v univ (fun _ _=>tallJ _ _)]; let e:= prio f (tou q (Phone G) false u) univ (Chart.jacobian P) (Chart.Ratio.jacobian_smooth hr) (fun i _=>CharterS ..) (winds' q hr u false (Phone G)); exact congr_arg (fun (z:ScriptJ T!)=> z∘ turn Q p) (show divergence f v univ*g+Flux f v univ g=0 from e)
-- charge shifted stamp
end YM.OPE.Merchant
