import YM.FVAAlt2.Plus.High
import YM.MS.Swirl.Migrate

/-! RichBook generalization. Adapted from `MS/Swirl/Migrate`. -/

set_option autoImplicit false
noncomputable section

-- Swirl/Migrate
namespace YM.MS.Swirl.Near
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom
open scoped Topology ContDiff Interval
variable {A E I W:Type} [AddCommGroup E][Module ℂ E] {G:Gauge}{i:I}{L:I→Side}{A':Faces I} {φ:Team}{n d:ℕ}{N:Side} {X:Actor G} {V: W→Actor G} [LinearOrder W] {b:Bool}{η:I→ℝ}
open SpaceOut
lemma billRentPl {B:Local.Physical.Deck G}(P: RichBook B)(p:Team)(v: Acts B d): Circle G ( Menus.rentPl P p v ) false 0 where
    stance0 _ _ h:=Bool.noConfusion h
    actual i x:= posesPl P p ..
    settled i x:= appearsPl P p v x i
    tag i:= rentReadyPl P p ..
    room i:=⟨ i+d,fun x=> by exact_mod_cast rentLimitPl P p v x i⟩
omit [LinearOrder W] in
lemma rankVPl {B:Local.Physical.Deck G}(t:Team)(U:RichBook B)(d:ℕ)(A:Acts B d)(x:ℝ): Menus.rentPl U t A x= car ( Y t x ) ( Menus.rentPl U (Stripped t) A x ):= by
    have he (t:Team): Menus.rentPl U t A x=∑ i:Glyph B d,pairW ( LinearMap.lsmul ℂ (Dot G Cover) ) (fun n=> oil A i n x) (Glyph.preamblePl U t i x):= funext (fun n=> by rw [Finset.sum_apply]; rfl);
    rw [ he t, he ( Stripped t ),map_sum ]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold Glyph.preamblePl; rw [ sWob ( t:=t ), oil_roll ]
end YM.MS.Swirl.Near
