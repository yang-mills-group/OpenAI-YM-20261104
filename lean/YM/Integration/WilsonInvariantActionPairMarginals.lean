import YM.Integration.WilsonInvariantActionPairHistory
import YM.Integration.WilsonInvariantActionPairPosterior

/-! Both nonlinear upper observables and their actual cutoff marginals
remain on the same Wilson ensemble throughout the ordered extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionPairMarginals
open Filter Function Set MeasureTheory Table Spec Climb Maxwell Maxwell.Free Trace.Pilot
open TraceExtension Next.UVStress PhysicalNext.Repeat.Legato Lattice RG Wilson RGComparison.Core16
open Extraction Extraction.Order Push.GridApprox OPE OPE.Orbits OPE.Therm
open WilsonInvariantActionPairHistory WilsonInvariantActionPairCovariance
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S)
variable (R) {N p : ℕ}

def single (a : R.family.label 4) (x : Site (R.family.side N p)) : ℂ :=
  R.family.numeric N p (fun _:Fin 1=>⟨4,a⟩) (fun _=>x)

theorem marginal (a : R.family.label 4) (x : Site (R.family.side N p)) :
    single R a x = ∫U,R.family.O N p a x U ∂scene R.family.path N p N := by
  rw [WilsonMacroscopicForwardTransfer.top (C:=R.family) R.makes N p]
  rw [single,Family.num]
  simp [Family.seen]

theorem translation (h : R.family.ref 4≤N) (a : R.family.label 4) (x : Site (R.family.side N p)) :
    single R a x=single R a (0:Site (R.family.side N p)) := by
  simpa [single] using R.family.anchored (p:=p) R.makes (fun _:Fin 1=>⟨4,a⟩)
    (fun _=>h) x (fun _=>0)

variable {R}
include F in
theorem converge (y : S.Field 4) :
    f.limits (fun _=>True) (fun N p=> single R (S.representative 4 y) (0:Site (R.family.side N p)))
      (expectation S 4 y) := by
  let v : Fin 1→R.family.book.Token:=fun _=>⟨4,S.representative 4 y⟩
  let z : Points 1:=0
  let K : Set (Points 1):={z}
  have compact : IsCompact K:=isCompact_singleton
  have cyclic (p : ℕ) : K⊆Cyclic R.family.S p 1 := fun _ _ i j hij=>False.elim (hij (Subsingleton.elim i j))
  have generic : K⊆YM.generic 1 := fun _ _ _ _ _ _=>Subsingleton.elim ..
  obtain ⟨P,local_,outer⟩:=F.room.generic
  have grid0 (N : ℕ) : grid R.family N (fun _:Fin 1=>(0:Cover))=z := by
    ext i a
    simp [grid,points,Schedule.gridPoint,z]
  have native : S.read z v=expectation S 4 y := by
    rw [←S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl)
      (show z∈conf 1 from fun i j _=>Subsingleton.elim i j) v]
    have project : S.classTokens ∘ v=fun _:Fin 1=>(⟨4,y⟩:S.Tag) := by
      funext i; simp [Table.classTokens,v,S.rep]
    rw [project,vev_coordinates F.room.kernel.translations]
    exact (onepoint S y).symm
  refine ⟨Eventually.of_forall fun _=>trivial,fun p=>(P p).read z v,fun p _=>?_,?_⟩
  · rw [Metric.tendsto_nhds]
    intro ε he
    filter_upwards [local_.onK p 1 K compact (cyclic p) v ε he] with i hi
    have e:=hi (fun _:Fin 1=>(0:Cover)) ((grid0 _).symm ▸ (show z∈K from mem_singleton _))
    simpa [grid0,dist_eq_norm,single,v] using e
  · rw [Metric.tendsto_nhds]
    intro ε he
    filter_upwards [outer 1 K compact generic v ε he] with i hi
    simpa [dist_eq_norm,native] using hi z (mem_singleton _)

end YM.Integration.WilsonInvariantActionPairMarginals
