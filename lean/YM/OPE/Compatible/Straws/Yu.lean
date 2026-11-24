import YM.OPE.Compatible.Straws.Lime
/-!
# Jet calculus along small paths of coarse parameters
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
local notation "Lf" => Tested.germ
open Radial ScriptJ JetS
namespace Stranded
open Arc Flock Pilot Coin
variable [FiniteDimensional ℝ E][FiniteDimensional ℝ F][MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)
variable {δ:ℝ→E}{a b:E}(h:Reads δ ⟨0,a,b⟩){x:ℝ→F}(hp:Gael x)
def surfer (u v w:E→Token)(x:E):=assembleJ (u x) (v x) (w x)
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in
lemma Bfray (p:Token): ScriptJ.B (fun _:E=>p):=fun _=>Bond.keep _
abbrev usher (δ:ℝ→E)(x:ℝ→F)(p:F×E→Token)(i:E):= mine fun t=> p (x t,i-δ t)
def glade (p:E→Token)(a:Token)(x:E):= a*p x
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in
lemma gladeB (p:E→Token)(hp:ScriptJ.B p)(a:Token): ScriptJ.B (glade p a):= ScriptJ.height (Bfray (E:=E) _) hp
lemma reed (p q v:E→ Token)(h:ScriptJ.B p)(hp:ScriptJ.B q)(hx:ScriptJ.B v): ScriptJ.B (surfer p q v)∧ draw (surfer p q v) L μ=assembleJ (draw p L μ) (draw q L μ) (draw v L μ):=by
    rw [show surfer p q v=p+glade q ski+glade v (ski*ski) from funext fun _=> rfl]; let A:=gladeB _ hp ski; let B:=gladeB _ hx (ski*ski); let H:= ScriptJ.key h A; refine ⟨ScriptJ.key H B,?_⟩; rw [duoS μ L _ _ H B, duoS μ L _ _ h A]; unfold glade; rw [drips μ L _ _ hp,drips μ L _ _ hx]
local notation "W"=> Warp L a b
local notation "σ"=> streak δ x
include h hp
lemma cider (p:F×E→Token)(hy:ScriptJ.B p):
    let w(t):= draw (fun y=> p (x t,y)) L μ
    let q:= usher δ x p
    ScriptJ.B q ∧ Reads (jur w) (draw (W*q) L μ) :=by
       obtain ⟨h1,h2,h3⟩:= ScriptJ.bondX hy; intro w q; let A(v):=(p v).s; let B(v):=(p v).l; let K(v):=(p v).h; have hv(f)(hb:Bond f):= vintage μ L h hp f hb; obtain ⟨HE,hS⟩:= hv A h1; obtain ⟨HY,hA⟩:= hv B h2; obtain ⟨HJ,hB⟩:= hv K h3
       have hh : q= surfer (σ A) (σ B) (σ K):=funext fun y=> Fitted.totals (Stalk h hp A h1 y) (Stalk h hp B h2 y) (Stalk h hp K h3 y) -- reduce
       rw [hh]; refine ⟨(reed μ L _ _ _ HE HY HJ).1,?_⟩
       rw [show (W*surfer _ _ _)= surfer (W*σ A) (W*σ B) (W*σ K) from (by funext i; simp only [Pi.mul_apply,surfer,assembleJ]; ring), (reed μ L _ _ _ (ScriptJ.height (warpB L a b) HE) (ScriptJ.height (warpB L a b) HY) (ScriptJ.height (warpB L a b) HJ)).2]; exact Fitted.assent hS hA hB
end Stranded
end YM.OPE.Libra
