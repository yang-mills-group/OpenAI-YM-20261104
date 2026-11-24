import YM.OPE.Compatible.Vino.Bliss
/-!
# clocks torque on column components.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Paver
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m l:ℕ}
variable {K:Sponsor G}{T:Seasons K}{v b:ℝ}
variable (P:Patch)(C:KernelChoices) (U:Boxes G P C) (A:Alps K T i v) (V:ChartRatio G)
variable (S:StepData c f)(he:Odd S.ratio.count.val) (t:S.Choices)(Z:Boxes G S.patch S.kernel)
local notation "X!"=> forest S.ratio he
variable (g:Bid.Dir G c→AxisChart G (forest S.ratio he))
variable (p:Site c)(x:Bid.Dir G c)(Y:FibreRep S he Z t (i:=i) A g b)
variable {F E:Type}
section stage
abbrev impulse (i:Phase)(x:Curtain I): Spring I:= Pi.single i x
lemma nip (i:Phase)(d k:ℕ)(p:Curtain I)(b:ℝ)(h:Volume p (d+i.val) k b): Tide (impulse i p) d k b:=by
     intro j; by_cases he:j=i
     · subst j; rw [show impulse _ _ i= p from Pi.single_eq_same ..]; exact h
     rw [show impulse i p j=0 from by simp [impulse,he]]; exact ⟨fun _ _=>rfl,fun _=> Sack.zero (Sack.coins (h.2 0)) _⟩
lemma impBox (w:Curtain (Shade G))(d:ℕ)(j:Phase)(x:Bid.Dir G c) (p:Site c): inkM (impulse j w) d p x= Ū^j.val* JetS.plainJ (Flair w (d+j.val) (spool G c x) p) :=by
    fin_cases j<;>apply JetS.eta <;> norm_num [Ū,JetS.seq, JetS.plainJ,go, inkM,impulse,pow_succ, Shell.flair0]
    · erw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne (by decide),Shell.flair0]
    · erw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne (by decide),Shell.flair0]
    erw [Pi.single_eq_same]
end stage
end YM.OPE.Cascade.Paver
