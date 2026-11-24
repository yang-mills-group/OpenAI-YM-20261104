import YM.QuadraticLocal.Found.Hence
import YM.Comparison.RG02.Bulk.Sequence
import YM.AllOrder.Floe.Slide
/-!
# Same-Regulator Fk orientation

Identify the unmarked Floe.Schematic input as the ENTIRE actual supplementary vacuum in
Fk. (not choosing W colors by fitting jets EACH level or marker). Extra.Packets rank ≥3 in fluctuation
degree, but maybe rank 2 for later additions. Caller provides admissible `hD`. No truncation of
Kin, unmasked.P.v.Piece here. Grows/gauge value integrated later. Proof addresses confusion about
likelihood and marks: zero-label Hessian etc built from S.forecast.Holds. We'll prove reveal of
FK coefficients inclusion of physical field.L.Scope. Future carry branch of λ as arbitrary colors
with *only vacuum field* replaced by render(D) closure MW. Needs to apply after order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Fk
open Function Filter Finset Lattice Wilson RG Pressure RG.Supply Input Org Precision
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open AllOrder AllOrder.Floe Extra.Iteration MeasureTheory
open Comparison.RG02 Comparison.RG02.Bulk Assembly
open Marker Extra.Trajectories Multi
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {f c:Side}{V:Type}[DecidableEq V] {J:Census V}
variable (M:Layout G)(A:Finset Age)
variable (h:Legal A M) (D:Colors J G f)

def money (t:ℝ): Config G f→ℝ:= ∑ i∈A, sketch M i f t
-- supply binds W.vac by Layout before later phase usage.

def grant : Colors J G f := { D with vac:= money M A }
-- regular.
local notation "S"=> money (f:=f) M A
include h in
lemma budget (t:ℝ) : Laplace.Toll f (S t):= by
   have he i (hh:i∈A): Laplace.Toll f (sketch M i f t) := by
      obtain ⟨z,C,hz,hC⟩:= h.rent i hh; apply Laplace.Toll.scale; refine ⟨?_,fun x U=>?_,fun s o U=>?_⟩
      · unfold Extra.Iteration.action RG.Patch.average; exact (Envelope.const _).mul (Envelope.sum _ _ fun i=> Push.SectorMeasure.Env.along (Laplace.env_uncut hC hz) (continuous_pull i 0|>.measurable)) -- Ns?
      · simp only [Extra.Iteration.action,Work.F05.pull_gauge_zero,Work.F05.uncut_gauge (M i) (h.symm i hh)]
      unfold Extra.Iteration.action Patch.average; apply congr_arg; conv_rhs=> rw [←Equiv.sum_comp (Equiv.mulLeft s)]
      refine Finset.sum_congr rfl (fun i _=>?_); dsimp only; rw [pull_pull,AnalyticNext.QuarticMatch.Joint.translate_by, AnalyticNext.QuarticMatch.Joint.uncut_translate]; rfl
   suffices H : ∀ B⊆A,Laplace.Toll f (money M B t) from H A (subset_refl _)
   intro B; induction B using Finset.induction with
   | empty=> intro _; rw [money,sum_empty]; exact ⟨Envelope.const 0,fun _ _=>rfl,fun _ _ _=>rfl⟩
   | insert i B hi H=> intro hx; rw [money,sum_insert hi]; exact (he i (hx (mem_insert_self ..))).add (H fun i h=> hx (mem_insert_of_mem h))
include h
-- authenticate x-stage input coupling powers. retain two stamps.EXTRA.No canonical chaos.
lemma stem (i:Age)(hh:i∈A): GradeAt (i.e+2) (projected (fun t=>sketch M i f t)):= by
    let L:= Extra.Iteration.action (M i) ∘ represent (G:=G) (n:=f)
    have ht : GradeAt i.r L:= (by obtain ⟨b,u,hb,hu⟩:= h.rent _ hh; exact ⟨action_smooth hb hu fun i=> Work.F03.represent_smooth (G:=G) i|>.contDiffAt,lower_jet hb hu⟩)
    rw [i.recovery]; exact (GradeAt.shifts Prod.fst contDiffAt_fst rfl i.stamp).mul (GradeAt.coarse ht (g:=Prod.snd) contDiffAt_snd rfl)
lemma level : GradeAt 5 (projected S):=by
    have he (B)(hB:B⊆A):GradeAt 5 (projected (money (f:=f) M B)):= by
       induction B using Finset.induction with
       | empty=> refine (GradeAt.grade_zero (X:=ℝ×Bid.Dir G f) (Y:=ℝ) 5).depends (Eventually.of_forall fun u=>?_); simp [money,projected]
       | insert i B hi H=>
          have hx := ((stem M A h (f:=f) i (hB (mem_insert_self ..))).lower (show 5≤ i.e+2 from Nat.add_le_add_right (Age.senior i) 2)).add (H (fun _ h=> hB (mem_insert_of_mem h))); refine hx.depends (Eventually.of_forall fun i=>?_); unfold projected money; rw [sum_insert hi]; rfl
    exact he A (subset_refl _)
-- W.mark explicit constructor; no requirement for this lemma its own vacuum density is precise. Replace vacuum.Ph.
lemma standard (hf:∀ i, GradeAt (D.power i) (projected (D.mark i))) (hh:∀ i t,GaugeInvariant (D.mark i t)) (he:∀ i t,Envelope (D.mark i t)): (grant M A D).Standard :=
   ⟨⟨(level (f:=f) M A h).lower (by decide),hf,fun t=>(budget M A h t).varnish,hh,fun t=>(budget M A h t).fit, he⟩,level M A h⟩
lemma well (hd:Well D) : (grant M A D).Standard := standard M A h D hd.suppose_mark hd.gauges hd.prices
end YM.QuadraticLocal.Fk
