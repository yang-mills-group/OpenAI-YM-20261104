import YM.AllOrder.Floe.Stars
import YM.Integration.LocalFormalAction
/-!
# Bind independent Fk prescription. Same complete vacuum & conditional norm
 Here kernels include *auxiliary* as well as actual. A constructor for vacuum ink
 (`Floe.Step.Path/Income`; snapshot supplement) has a period table. These theorems
 prove it's exactly the `Bulk` prescription of Datum with the corresponding Colors.vac.
 Frame costs & knit of its analytic presentation in later files. *No resetting* here.
 Discrepancy of previous step models not among the Colors; earned separately (`Peak`) etc.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Binding
open Function Filter Lattice RG Wilson Tree Precision Input Gauge Finset MeasureTheory
open Push Push.Uniform SectorMeasure PhysicalNext Repeat Lapis
open ConnectedActivityE6 Blaze Brush Next.SectorChange Laurent Exterior Org
open Work.F03 Work.F05
open Marker Multi Comparison.RG02.Order
open AllOrder AllOrder.Floe Laplace Response Ink
open PertExtension.Series Radial PositionX.Jet PositionX.Gauss Extra.Iteration
open Comparison.RG02.Assembly Comparison.RG02.Bulk
open scoped BigOperators Topology ENNReal Classical InnerProductSpace MatrixOrder ContDiff Matrix.Norms.Frobenius
variable {G: Gauge} {c f n: Side} {S:StepData c f} {k t j:ℕ}
    {V:Type} [DecidableEq V] {B:Census V}

section entrance
variable (W : Floe.Layout G)(U:Finset Age)(w:Colors B G n)
/-- Frozen vacuum exponent supplements, BEFORE `g^-2`. Don't set the loop bank to zero. -/
def drawn (n:Side)(b:ℝ) : Config G n→ℝ:= ∑ i∈U, sketch W i n b
def plant : Colors B G n := {w with vac:=drawn W U n}
lemma sketch_grade (h:Legal U W) (i:Age)(hv:i∈U) : GradeAt (i.e+2) (projected (sketch W i n)):= by
 obtain ⟨b,c,hb,hC⟩:=h.rent i hv; rw [i.recovery]; let z:= fieldDir G n 1
 have ht :GradeAt i.r (Calibration.acted (n:=n) (W i)):=⟨Calibration.acted_jet _ hb hC,lower_jet hb hC⟩
 exact GradeAt.mul (GradeAt.shifts Prod.fst contDiffAt_fst rfl _) (ht.coarse (g:=Prod.snd) contDiffAt_snd rfl)
lemma planted (h:Legal U W) : GradeAt 5 (projected (drawn W U n)):= by
 have hv:=GradeAt.list_sum U (fun i=>projected (sketch W i n)) (k:=5) (fun i hi=>(sketch_grade W U h i hi).lower (by have hx:=i.senior; omega)); unfold Comparison.RG02.Bulk.projected drawn; simp_rw [Finset.sum_apply]; exact hv
lemma barren (h:Legal U W) (b:ℝ) (i:Age)(hv:i∈U) : Laplace.Toll n (sketch W i n b):= by
 -- same as Floe.orchestra, retain per label.
 obtain ⟨s,C,hc,hξ⟩:= h.rent i hv; apply Laplace.Toll.scale; refine ⟨?_, fun x _=>?_, fun v _ _=>?_⟩
 · unfold Extra.Iteration.action Patch.average; exact (Envelope.const _).mul (Envelope.sum _ _ fun i=> Env.along (env_uncut hξ hc) (continuous_pull i 0 |>.measurable))
 · simp only [Extra.Iteration.action, Work.F05.pull_gauge_zero, Work.F05.uncut_gauge (W i) (h.symm i hv)]
 unfold Extra.Iteration.action Patch.average; apply congr_arg; conv_rhs=> rw [←Equiv.sum_comp (Equiv.mulLeft v)];
 refine Finset.sum_congr rfl fun i _=>?_; dsimp only; rw [pull_pull,AnalyticNext.QuarticMatch.Joint.translate_by, AnalyticNext.QuarticMatch.Joint.uncut_translate]; rfl
lemma standard (h: Legal U W) (hx: Well w) : (plant W U w).Standard:= by
 have hp t : Laplace.Toll n (drawn W U n t):= by
   suffices hh: ∀ Q⊆ U,Laplace.Toll n (∑ i∈Q,sketch W i n t) from hh U (le_refl _)
   intro Q hQ; induction Q using Finset.induction_on with
   | empty=> rw [Finset.sum_empty]; exact ⟨Envelope.const 0,fun _ _=>rfl,fun _ _ _=>rfl⟩
   | insert i S hh ih => rw [sum_insert hh]; exact (barren W U h t i (hQ (mem_insert_self ..))).add (ih (fun k hk=> hQ (mem_insert_of_mem hk)))
 exact ⟨⟨(planted W U (n:=n) h).lower (by decide),hx.suppose_mark,fun b=> (hp b).varnish,hx.gauges,fun b=> (hp b).1,hx.prices ⟩, planted W U h⟩
lemma sample : (Comparison.RG02.Bulk.Colors.noHole (V:=V) G n B).Standard:= Comparison.RG02.Bulk.Colors.no_hole .. -- remove
end entrance
end YM.Qlocal.Binding
