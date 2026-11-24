import YM.AllOrder.Floe.Cascade
import YM.AllOrder.Iron.Entries
import YM.Extra.ITERATION_NO_LOSS.Inherited
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge} {c f n : Side} {k j w N : ℕ} {S:StepData c f}
variable {σ C Z D β Θ:ℝ}
structure Age where
 grade : ℕ -- EXTRA only starting at 3. assign clover ranking.
 slots : ℕ -- offset from 2
 paid : slots≤grade+3
 deriving DecidableEq
namespace Age
abbrev e (x:Age) := x.grade+3
abbrev r (x:Age) := x.slots+2
def stamp (x:Age):= x.e+2-x.r
abbrev leader (x:Age):= (x.grade, x.e-x.slots)
lemma recovery (x:Age): x.e+2=x.stamp+x.r:= Eq.symm (Nat.sub_add_cancel (Nat.add_le_add_right x.paid 2))
lemma senior (u:Age): 3≤u.e:= by unfold e; omega
lemma pricey (x:Age): x.r ≤ x.e+2:=Nat.add_le_add_right x.paid _
-- fleet availability
lemma finite_scope (e:ℕ): Set.Finite {x:Age| x.e ≤ e}:= by
 let f:Age→ ℕ×ℕ:= fun x=>(x.e,x.slots)
 have he:Injective f:= by rintro ⟨x,k,h⟩ ⟨x',k',h'⟩ hi; obtain ⟨rfl,rfl⟩:=show x=x'∧k=k' from ⟨Nat.add_right_cancel (Prod.mk.inj hi).1,(Prod.mk.inj hi).2⟩; rfl
 apply Set.Finite.subset (((Set.finite_Iic e).prod (Set.finite_Iic e)).preimage he.injOn); intro x (hx:x.e≤e); exact ⟨hx,x.paid.trans hx⟩
def scope (e:ℕ):= (finite_scope e).toFinset
@[simp] lemma in_scope {i:Age}: i∈scope k ↔ i.e≤k:= (finite_scope k).mem_toFinset
-- operations used to mask
end Age
local notation "I"=>Age
abbrev Layout (G:Gauge) := (i:Age)→ ℕ→ Atom G i.r
variable (F:Forest S.ratio) (R:PathData G) (p:Clip)
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "X"=> Apex c G × Y
local notation "E"=> ℝ × X
variable (P : Layout G) (o:ChartRatio G)(t:S.Choices) (T:Finset Age)
-- Signed input. constant power ^ so nonmaterial β formula integral. Note T subset before...
def sketch (i:Age)(n:Side)(v:ℝ):= v^i.stamp • Extra.Iteration.action (n:=n) (P i)
def audition (v:ℝ):= primitive (f:=f) R p v+ ∑ i∈T, sketch P i f v
-- Express additional analytic exposure of fine curvature in tree slice coordinates. `star` near. prove via occurrence jets to support cost.
def far (i:Age): X→ℝ:= Extra.Iteration.action (P i) ∘ ((fine G F) ∘ combineH (G:=G) F)
-- Body budgets strictly tied rank. no stages included.
structure Legal (T:Finset Age)(P:Layout G):Prop where
 rent i : i∈T→ ∃ a C:ℝ,0<a∧ Charged (P i) a C
 symm i : i∈T→ SymmetricAtoms (P i)
variable (hp : Legal T P) {i:Age} (hi:i∈T)
include hp
lemma orchestra (b:ℝ) (h:R.Bounds p σ C Θ): Laplace.Toll f (audition (f:=f) R p P T b):= by
 unfold audition; apply Laplace.Toll.add (e:=Laplace.primitive (f:=f) R p b) ((toll_main h).add ((toll_loop h).scale (b^2)))
 have he i (ht:i∈T) : Laplace.Toll f (sketch P i f b) := by
     obtain ⟨t,C,hc,h⟩:= hp.rent i ht; apply Laplace.Toll.scale; refine ⟨?_,fun x U=>?_,fun s o U=>?_⟩
     · unfold Extra.Iteration.action Patch.average; exact (Envelope.const _).mul (Envelope.sum _ _ fun i=> Env.along (env_uncut h hc) (continuous_pull i 0|>.measurable))
     · simp only [Extra.Iteration.action,Work.F05.pull_gauge_zero,Work.F05.uncut_gauge (P i) (hp.symm i ht)]
     unfold Extra.Iteration.action Patch.average; apply congr_arg; conv_rhs=> rw [←Equiv.sum_comp (Equiv.mulLeft s)]; -- terms
     refine Finset.sum_congr rfl fun i _=>?_ ; dsimp only; rw [pull_pull,AnalyticNext.QuarticMatch.Joint.translate_by, AnalyticNext.QuarticMatch.Joint.uncut_translate]; rfl
 let H W:=Laplace.Toll f (∑ i∈W, sketch P i f b); have hc W (hX:W⊆T): H W:= by
    induction W using Finset.induction_on with
    | empty=> unfold H; rw [Finset.sum_empty]; exact ⟨Envelope.const 0,fun _ _=>rfl,fun _ _ _=>rfl⟩
    | insert i S hh ih => unfold H; rw [sum_insert hh]; exact (he _ (hX (mem_insert_self ..))).add (ih (fun k hk=> hX (mem_insert_of_mem hk)))
 exact hc T (subset_refl _)
-- no small geometry here. Certified lower order of far after lifting & chart.
def slid : X → Work.F03.ChartVars F G := fun p=> (paint F G) (combineH F p)
def slidL: X ≃L[ℝ] Work.F03.ChartVars F G:= (combineH (G:=G) F).trans (paint F G)
include hi
lemma far_capsule : ContDiffAt ℝ ω (far F P i) 0 ∧ ∀ j < i.r,iteratedFDeriv ℝ j (far F P i) 0=0:= by
 obtain ⟨a,C,hC,h⟩:= hp.rent i hi; let X' := Work.F03.ChartVars F G; let T:X'→ Bid.Dir G f:= Work.F03.axisLog F; let f₁:= T ∘ slid (G:=G) F; let g : Bid.Dir G f→ℝ:=Extra.Iteration.action (P i) ∘ represent
 let D: X'→ X':= id; have hf:ContDiffAt ℝ ω T 0:= (Work.F03.inclusion_smooth (G:=G) F).snd; have ht : slid (G:=G) F= (slidL (G:=G) F):=rfl; have he:f₁ 0=0:= by unfold f₁; rw [Function.comp_apply,ht,map_zero]; exact congr_arg Prod.snd (Work.F03.inclusion_zero (G:=G) F)
 have hx:ContDiffAt ℝ ω f₁ 0:= by unfold f₁; rw [ht]; exact ((map_zero (slidL (G:=G) F)).symm ▸ hf).comp _ ((slidL F).contDiff.contDiffAt)
 have hh: g ∘ f₁=ᶠ[𝓝 0] far F P i:= by
     have hL:Tendsto (slid (G:=G) F) (𝓝 0) (𝓝 0):= by rw [ht]; rw [← show slidL (G:=G) F 0=_ from map_zero _]; exact (slidL F|>.continuousAt)
     filter_upwards [hL.eventually (Work.F03.inclusion_works (G:=G) F)] with x h; exact congr_arg (Extra.Iteration.action (P i)) h
 have hG: ContDiffAt ℝ ω g 0:= action_smooth hC h fun i=> Work.F03.represent_smooth (G:=G) i|>.contDiffAt; refine ⟨((he.symm ▸ hG).comp _ hx).congr_of_eventuallyEq hh.symm,fun j hj=> ?_⟩
 let Q:= fderiv ℝ f₁ 0; rw [← (hh.iteratedFDeriv ℝ j).self_of_nhds, Jets.tangent (f:=g) (d:=i.r) (hG.of_le le_top) (hx.of_le le_top) he (lower_jet hC h) j hj.le, Next.Foundations.jets_linear Q (hG.of_le le_top),show iteratedFDeriv ℝ j g 0=0 from lower_jet hC h j hj]; rfl
end YM.AllOrder.Floe
