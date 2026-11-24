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
# Vanishing of the phase-zero projection

If the phase-zero component of `x` belongs to `tLead D₀`, `Lead_kill` proves
that `Energy 0 W` vanishes on `FirP D j' x`. The proof applies `Gift` twice
to move this component to phase two, where `pillarK` puts the resulting
vector in the terminal flag and `FinAura` gives vanishing.
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
local notation "V!*" => Drift.Turns D₀

section
variable {L:Fin 3→Type} [∀ i,NormedAddCommGroup (L i)] [∀ i,NormedSpace ℝ (L i)] {E:ℕ→Type} [∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,CompleteSpace (E i)]
lemma utterQ {Yt:Mints L→L[ℝ] Mints L} {μ':ℕ→ℝ}(y:Fruition Yt (μ' e)){v z c:ℝ}{T:(i:Fin 3)→Cuts r μ' v z (L i) E}(hp:Assist T Yt)(ht:e<r)(hb:∀ i,ShadeR (T i) (e+1) c)(h:trims 2 y.val)(he:(T 2).Tap e (y.val 2)=0):y=0:=by
       apply Subtype.ext; apply trims.limb; apply shineZ T hp ht hb 3 le_rfl y.val y.property; intro i _; fin_cases i; exact (congr_arg ((T 0).Tap e) (h 0 (by omega))).trans (map_zero _); exact (congr_arg ((T 1).Tap e) (h 1 (by omega))).trans (map_zero _); exact he
end
lemma pillarK (x:F!)(hv: trims 2 x)(hz: x (2:Phase)∈ (Drift.Turns D₀ 2).flag e)(ht:e ≤ l+1) (i:M) : x∈ U.flag e i:=by
       induction e with
       | zero=> rw [U.first]; exact Submodule.mem_top
       | succ e ih=>
            let j:= (Drift.Turns D₀ 2); obtain ⟨h,hQ⟩:=(j.next e ht _).1 hz; let v:U.flag e i:= ⟨x, ih h (by omega)⟩; apply (U.depth e i ht v).2; let y:= U.read e ht i v; obtain ⟨ht',hZ,hX⟩:= U.quake e ht i v 2 hv; have hh:= Z.bill e ht; exact utterQ y hh.HB ht hh.chip hZ (hX.trans hQ)
-- Two applications of `Gift` carry the phase-zero component to phase two.
noncomputable abbrev tLead (K':Stern K P τ l d w):= fillet G d (τ 0) (l+1) (Nat.add_le_add_right (sternCap K' 0).le 1)
lemma hider (x:F!)(h:x (0:Phase)∈ tLead D₀):
      Gift G D₀.aware (Gift G D₀.aware x) 2∈ (Drift.Turns D₀ 2).flag (l+1):=by
       have ht:l+1≤ τ 2:= sternCap D₀ _; let D:= Gift G D₀.aware; let F:=D x; change D F 2∈ _; rw[show (Drift.Turns D₀ (2:Phase)).flag (l+1)=fillet G (d+(2:Phase).val) (τ 2) (l+1) (by omega) from by simp only [Drift.Turns, tuneG,min_self]]; erw [show _= _ from tack1 D₀.aware F 1 2 rfl]; rw [show F 1= _ from tack1 D₀.aware x 0 1 rfl]; apply (decrement _).2; intro i; erw[TurnL D₀.aware 1 2,TurnL D₀.aware 0 1]; exact (decrement (k:=d) (x (0:Phase))).1 h i
lemma Lead_kill (x:F!)(h:x (0:Phase)∈ tLead D₀): Energy 0 W (FirP D j' x)=0:=by
       let z:= Gift G D₀.aware; let f:=z (z x); have hp: trims 2 f:=by intro j hj; fin_cases j; exact tack ..; change f (1:Phase)=0;rw [show f 1= _ from tack1 D₀.aware (z x) 0 1 rfl,show z x 0= _ from tack D₀.aware x,map_zero];exact False.elim (Nat.lt_irrefl 2 hj)
       have he:= (FinAura D j' f).1 (Submodule.mem_sup_left (pillarK f hp (hider x h) le_rfl j')); let V:= FlowP (Eagle Hp Z a W); have ht : Energy 2 W (FirP D j' f)= _ := (show Energy 2 W (FirP D j' f)=Energy 0 W (FirP D j' x) from ?_); swap
       · exact (congr_arg (Energy 2 W) ((RiseZip D j' (z x)).trans (congr_arg V (RiseZip D j' x)))).trans rfl
       exact ht.symm.trans ((congr_arg (Energy 2 W) he).trans (map_zero _))
end
end YM.OPE.Stroke
