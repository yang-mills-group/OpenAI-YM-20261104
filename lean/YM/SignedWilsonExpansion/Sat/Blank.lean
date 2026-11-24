import YM.SignedWilsonExpansion.Kane.Finale
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.SignedWilsonExpansion.Kane
open Function Filter Set Table Spec Climb Trace Trace.Pilot PhysMS PhysMS.Frame
open Extraction Order Spin Next.UVStress OPE OPE.Orbits Levy
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 Dframe FVA2.Scale.Level Future
open Belfry Belle Dancer Belfry.Crisis Belfry.Classroom Belfry.ScaleFits Commission
open scoped BigOperators Topology ContDiff Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(W:ℝ→tower S)(L:Leading F W)
variable {b d e j n:ℕ}{ι:Type}{l:Filter ι}{g r ε:ι→ℝ}
namespace Tilted
open FVA2.Scale Belfry.Crisis Asymptotics Path
open MS MS.Land MS.Fleet MS.Native FVA2.Scale
namespace None
open Dancer.Drawing Dframe Scale FVA2.Scale.Facets Equator Fleet
open MS MS.Theater MS.Local.Physical MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Mom MS.Puff.Actors
open FVA2.Arrival PowerSeries
variable {P:Normalize.Store G}(U:Initialize G)(K:Rose.Pick P){T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{S':Prescription (Press.portDeck G)}(Q:Speed.Quoted U K T S') (s:G.Simple)
variable (x:Stage 0)(q:Tags G d 0)(c:ℝ)
local notation "Z" => (FVA2.Scale.Measure.start U K d)
lemma cheer_none (h: Finset (Fin 0)→ℕ→ℂ)(i:ℕ) : bouquet h Finset.univ i= if i=0 then 1 else 0:=by
   change ((( Trunk.stack ( SplitP.marked _ ) ).cheers h ( Finset.univ (α:=Fin 0) ).card ) Finset.univ i)= _; have he:(Finset.univ:Finset (Fin 0)).card=0:= rfl; rw [he,cheers,Finset.sum_range_succ,Finset.sum_range_zero, zero_add,MS.Puff.Dynamics.firstW]; -- inspect
   change ((SplitP.marked (Fin 0)).refineV Trunk.unit _) _= _; rw [SplitP.refineV,if_pos (Subsingleton.elim _ _)]; simp [Trunk,Actors.stack,SplitP.refineV,Toy,useN,SplitP.nat]
lemma none_waves (i:ℕ) : wave c T d 0 x i q= if i=0 then 1 else 0:= by
   let z : Fin 0→ Toon G d:= fun i=> Fin.elim0 i; rw [show q=fill z from Subsingleton.elim _ _]; unfold Equator.wave; rw [ribbon]; unfold continuum Landing.moondye Dial.tour; exact cheer_none ..
def EmptyW (Y:Way G d): Prop:= ∀ i (x: Stage 0)(q:Tags G d 0), Y 0 x i q= if i=0 then 1 else 0
variable {Y:Way G d}
lemma emptyStep (h:EmptyW Y)(p:Cn): EmptyW (couple p Y):=by
    intro i x q; rw [couple,translate,rules,Finset.sum_eq_single 0]; · rw [ h ]; simp [cut]; -- defs
    · intro j _ k; rw [h]; simp [k]
    simp
lemma singletonBudget (i:ℕ) : tally i 0 = {Finsupp.single none i}:=by
    ext x; have he: ∑ j, x j=x none:= by
        rw [Finset.sum_eq_single none]; · intro j _ h; exact False.elim (h (Subsingleton.elim _ _))
        (intro ht; exact False.elim ( ht ( Finset.mem_univ _ )))
    rw [totaled,he,Finset.mem_singleton]; constructor
    · intro h; refine Finsupp.ext fun i=> ?_; rw [Subsingleton.elim i none,Finsupp.single_eq_same]; exact h
    rintro rfl; simp
lemma emptyAct (h:EmptyW Y)(p:Guard G d): EmptyW (actMark p Y):=by intro i x q; rw [actMark,seen,singletonBudget,Finset.sum_singleton,Finsupp.single_eq_same,h]
include Q s
lemma emptyP : EmptyW Z:=by obtain ⟨a,b,c⟩:= Q.toContract.toMission.born; rw [← Measure.together U K 0 T S']; exact emptyAct ( emptyStep ( fun i x q=> none_waves x q 0 i ) _ ) _; all_goals assumption
lemma quiet : Path.mote Z b x.val c q=1:=by unfold Path.mote; simp_rw [Jury.exactC, emptyP U K Q s _ x q]; rw [Finset.sum_eq_single 0]; simp; (intro i h p; simp [p]); simp
omit Q s
variable {F W}
lemma pride (x:Points 0) (i:ι) : levelOf F W r i d 0 x q= 1:= by
   exact F.room.kernel.laws.trivial ( fun j:Fin 0=> ⟨ d,S.representative d (walk W (r i) d (q j)) ⟩ ) (r i • x)
end None
end Tilted
end YM.SignedWilsonExpansion.Kane
