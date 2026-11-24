import YM.MSbar.Diagram.Readers
/-! Dimensional current balance per Static symbol grade. Implements homogeneous scaled Ward ports
with only kinetic *polynomial* condition (at *all integers*) pending choices of C,A etc. Later
will discharge for gauge spectrum. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Diagram.WardOps
open Super Domain Domain.DR Loops Dim Symbol Function Set Filter MeasureTheory Arrow Clear
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {C:Type} {W:Edition C} {R T : ℝ} (z:ℂ) {P D Q: Sites C} {F G: Vertex C} {d k l:Bit}
variable (hp:Window W 0 R P) (hv:Window W d T D)
  (hq:Pilot univ 0 W d (liftS Q))(he:∀ i, D i= Loops.shift (W.binary i) (W.members i) d (Q i) (P i))
local notation "A" => traceP W z P
local notation "J" => traceP W z D
local notation "Hr" => traceR W z Q
local notation "B" => traceT W 0 z P
local notation "K" => traceT W 0 z D
include hv
lemma boreal (hf: Live W k F)(hG:Live W l G): traceT W k z D F G=sign k l• traceT W l z D G F:=congr_fun (on_pair hv.fit hv.bounded hf hG) z
include hp hv
lemma unary (H : Live W k F): A (J F)=J (A F):=by
   have hh:= congr_fun (on_loop hp.fit hp.bounded hp.space hv.fit hv.bounded hv.space H) z; simp only [atP] at hh; exact hh
section
variable (hf:Live W 0 F)
include hf
lemma tandem: A (K F F)+(2:ℂ) • B F (J F)=J (B F F)+(2:ℂ) • K F (A F):=by
    have hh:= congr_fun (on_density hp.fit hp.bounded hp.space hv.fit hv.bounded hv.space hf) z; simp only [atP,atT,Pi.add_apply,Pi.smul_apply] at hh; exact hh
lemma third : B F (K F F)= K F (B F F):=by
   have hh:= congr_fun (on_join hp.fit hp.bounded hv.fit hv.bounded hf) z; simp only [atT] at hh; exact hh
end
include hq he
lemma quality (H : Live W k F): Hr (A F)- A (Hr F)= J F:=by
   have hh:= congr_fun (on_current hp.fit hp.bounded hp.space hv.fit hv.bounded hv.space hq he H) z; simp only [atP,atR,Pi.sub_apply] at hh; exact hh
lemma expected (H : Live W 0 F): Hr (B F F)= K F F+(2:ℂ) • B F (Hr F):=by
   have hh:= congr_fun (on_leg hp.fit hp.bounded hv.fit hv.bounded hq he H) z; simp only [atT,atR,Pi.add_apply,Pi.smul_apply] at hh; exact hh
end YM.MSbar.Diagram.WardOps
