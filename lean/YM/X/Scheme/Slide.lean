import YM.X.Scheme.Report
import YM.X.Jet.Solve
/-!
Detector implicit equation supplies exact near-frame and inverse for D. Differential of full test solve at white; chart coordinate branch finite, independent of any mesh/schedule.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX
open Function Filter Set Pert Pert.Position Jet
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} (F:Labels.Frames G) {d n : ℕ}
local notation "W" => E F d
local notation "L"=> Buffer F d
local notation "Y"=> pureBank F d

-- matrix path (used for any patch verification at regulator)
lemma pulse (p:W)(b:L) : HasDerivAt (fun t:ℝ=>frameC F (t • b) p) (b.val p) 0:= by
   convert! (((hasDerivAt_id' (0:ℝ)).smul_const (b.val p)).const_add p) using 1; simp

def lightBank (w: MultilinearMap ℂ (fun _ : Fin n=> E F d) ℂ): ContinuousMultilinearMap ℂ (fun _ : Fin n=>W) ℂ:=
 ⟨ w, by
    let a : Lens F d n:= fun p=> w (baring F d ∘ p); have he:emerge F a=w:= Module.Basis.ext_multilinear (fun _=>baring F d) (fun i=> reads_emerge ..)
    rw [←he]; change Continuous fun p=> Bare.spread (baring F d) a p; simp_rw [Bare.spread_value]; refine continuous_finsetSum _ fun i hi=>Continuous.mul_const (continuous_finsetProd _ (fun j _=>?_)) _; fun_prop⟩ -- likely not
lemma project_move (b:L)(w:Bank F d)(s:Section F d): HasDerivAt (fun t:ℝ=>project F s (market F (t • b) w)) (project F s (jacBank F w b)) 0:= by
   suffices H:HasDerivAt (fun t:ℝ=>lookie F s (market F (t • b) w)) (lookie F s (jacBank F w b)) 0 from Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 H
   let v:= (lightBank F (w s.r s.f)).restrictScalars ℝ; let x (t:ℝ) := frameC F (t • b) ∘ s.p
   have he : x 0=s.p:= by
      have hb:(0:ℝ) • b=0:= by exact zero_smul ℝ b
      unfold x; rw [hb,frameC_zero];rfl
   have hh: HasDerivAt (v ∘ x) (v.linearDeriv s.p (b.val ∘ s.p)) 0 := by rw [←show x 0=s.p from he]; exact (v.hasFDerivAt _).comp_hasDerivAt 0 (show HasDerivAt x (b.val ∘ x 0) 0 from (by rw [he]; exact hasDerivAt_pi.mpr (fun i=> pulse F (s.p i) b)))
   rw [jacBank_eval]; rw [ContinuousMultilinearMap.linearDeriv_apply] at hh; exact hh

variable {F}
lemma interest_pays {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X] (b:L)(w:Bank F d){f:Bank F d→ₗ[ℝ] X}(h:f∈tableSpace F d X): HasDerivAt (fun t:ℝ=> f (market F (t • b) w)) (f (jacBank F w b)) 0:= by
   induction h using Submodule.span_induction with
   | mem v he=> obtain ⟨x,rfl⟩:=he; exact (project_move F b w x.1).smul_const x.2
   | zero=> exact hasDerivAt_const _ _
   | add x y hx hy h g=> exact h.add g
   | smul r y _ h=> exact h.const_smul r

namespace Detector
variable (D:Detector F d)
abbrev rail := Rail.surveyor D
abbrev Capture := D.rail.Target
abbrev read : Bank F d →ₗ[ℝ] Capture D:= D.rail.common
def parameter : Capture D:= D.read (pureBank F d)
lemma chartD (v:Bank F d)(b:L): D.rail.tableMap (D.read v,b)=D.D (market F b v):= (Rail.atMarket _ _ _).symm.trans (DFunLike.congr_fun (Rail.runs D).choose_spec _)
lemma chart_unit : D.rail.tableMap (D.parameter,0)=D.D (pureBank F d):= (chartD ..).trans (congr_arg D.D (market_zero ..))
lemma chart_move (v:L): HasDerivAt (fun t:ℝ=> D.D (market F (t • v) (pureBank F d))) v 0:= by
   have he:= interest_pays (X:=(Buffer F d)) v (pureBank F d) (by exact D.finiteD); rw [show D.D (jacBank F (pureBank F d) v)=v from DFunLike.congr_fun D.fixed v] at he; exact he
lemma chart_submerges : Jet.Submerge D.parameter D.rail.tableMap:= fun v=> (by unfold parameter; simp_rw [chartD]; exact D.chart_move v)

def slips : Capture D × Buffer F d→ Buffer F d:= (Jet.open_up D.parameter D.rail.tableMap D.chart_submerges D.rail.tableMap_smooth).choose
lemma slip_spec: Reports (Jet.center D.rail.tableMap) (D.parameter,0) 0 D.slips := (Jet.open_up D.parameter D.rail.tableMap D.chart_submerges D.rail.tableMap_smooth).choose_spec
end Detector
end YM.PositionX
