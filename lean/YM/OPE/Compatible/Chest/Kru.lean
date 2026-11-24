import YM.OPE.Compatible.Chest.Tor
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
# Phase projections of the transported readout

`Eψ` projects the transported map `Eout` to one phase. `shifts` identifies
the projection in the next phase after applying `trellisA` with the original
projection. Under `Stone`, `selection` writes the phase-two readout as a sum
of three maps through `StageM`, each with a polynomial norm bound in `Y`.
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
-- `Energy` takes the same phase projection at every retained level.
noncomputable abbrev OrthoC (W:GlowPack Hp Z a (k:=k)) :=(j:Fin (l+1))→ Eagle Hp Z a W j
variable (u': Phase)
noncomputable def Energy (W:GlowPack Hp Z a (k:=k)) : LineCt W→L[ℝ] OrthoC W:=ContinuousLinearMap.pi fun j=> ContinuousLinearMap.proj u' ∘L (ContinuousLinearMap.proj j)
noncomputable def Eout : solar G d τ→L[ℝ] LineCt W:= FirP D j' ∘L (Fallix G D₀.aware K (V j').gear hp).symm.toContinuousLinearMap
noncomputable def Eψ := Energy u' W ∘L Eout D j'
lemma Ecost : Wealth (fun j=> Eψ D j u') Y 1:=PledgeW (wealthC (X:=Y) (Energy u' W)) (PledgeW (pricedA' Hp Z a W U hq hp V D) (FallWeather (K:=K) D₀.aware _ hp Y hq).2)
lemma ΦBud (h:Stone Z Y U) :Docked (fun i=> (V i).gear) hp (fun j=> Eψ D j u') (l+1) 3 K:=by
       constructor
       · intro i p hv; let L:= Fallix G D₀.aware K (V i).gear hp; have he: TrueRay (L:=K.K) (V i).gear hp (L (L.symm p)).val (l+1):=(by rw[L.apply_symm_apply];exact hv); exact (congr_arg (Energy u' W) (awayK D i h (L.symm p) (secs (V i).gear hp D₀.aware (L.symm p) he))).trans (map_zero (Energy u' W))
       intro v p hv; rw[show p=0 from Subtype.ext (funext fun i=>hv i i.isLt),map_zero]
lemma Ming (p:solar G d τ): Eout D j' (trellisA G D₀.aware p)= FlowP (Eagle Hp Z a W) (Eout D j' p):=by
       let L:= Fallix G D₀.aware K (V j').gear hp; let b:=L.symm p; have he:L b=p:=L.apply_symm_apply _; have hh: L.symm (trellisA G D₀.aware p)=Gift G D₀.aware b:= L.injective ((L.apply_symm_apply _).trans ((congr_arg (trellisA G D₀.aware) he).symm.trans (Flick D₀.aware (V j').gear hp b (K:=K)).symm)); exact (congr_arg (FirP D j') hh).trans (RiseZip D j' b)
lemma shifts (y u':Phase)(hy:y.val+1=u'.val)(p:solar G d τ): Eψ D j' u' (trellisA G D₀.aware p)= Eψ D j' y p:=by
        have hh : Energy u' W (FlowP (Eagle Hp Z a W) (Eout D j' p))= Energy y W (Eout D j' p):=by fin_cases u'<;>fin_cases y<;> first|contradiction|rfl
        exact (congr_arg (Energy u' W) (Ming D j' p)).trans hh
-- Apply the three-phase factorization to the phase-two readout.
set_option maxHeartbeats 200000 in
lemma selection (h:Stone Z Y U):∃ S:M→ Terra G τ d 2→L[ℝ] OrthoC W, ∃ T:M→ Terra G τ d 1→L[ℝ] OrthoC W, ∃ F:M→ Terra G τ d 0→L[ℝ] OrthoC W, Wealth S Y 1∧Wealth T Y 1∧ Wealth F Y 1 ∧
       (fun j=> Eψ D j 2)=beneath (K:=K) (e:=l+1) (fun i=> (V i).gear) hp 2 S+beneath (K:=K) (e:=l+1) (fun i=> (V i).gear) hp 1 T+beneath (K:=K) (e:=l+1) (fun i=> (V i).gear) hp 0 F:=by
        apply Trinity D₀.aware _ _ _ hq (Ecost D 2) (ΦBud D 2 h)
end
end YM.OPE.Stroke
