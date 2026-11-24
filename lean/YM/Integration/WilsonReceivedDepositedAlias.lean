import YM.Integration.WilsonThermometerUnitNames

/-! Each earlier connected component becomes one temporary source at its own site. A
component's outputs are relabeled by all its previous names before evaluating the
ordinary or connected polynomial. The complete original rough vacuum is admitted. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedAlias
open Function Filter Finset MeasureTheory Relation Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Ribbon Menu Marker Ac GridApprox.Nil
open Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Ribbons Ribbons.Fibers Ribbons.ManyCopies
open Ribbons.ManyCopies.Muster RG05Readout RG05Readout.Address RG05Readout.Many
open Multi
open scoped Classical BigOperators
variable {V Z:Type}[Fintype V][DecidableEq V][Fintype Z][DecidableEq Z]
  (J:Census V)(name:Z→Multi.Hot J)
local notation "A" => Stock.census Z

omit [Fintype V] in
theorem permit : License (parts J) (A) name:=fun _ _=>Finset.mem_powerset.mpr (Finset.subset_univ _)

def fold : Poly (A) →ₐ[ℂ] Poly J :=
  (substitute J).comp (feed (fun _:Z=>1) (permit J name))

omit [Fintype V] in
theorem single (z:Z)(c:ℂ):
    fold J name (Poly.send ((A).fire z) c)=Poly.send (name z).val c:=by
  rw [fold,AlgHom.comp_apply,feed_fire,one_mul,substitute_apply,substituteL_send,unionOf_single]

def entered (f:Z→ℂ):Poly J:=∑z:Z, Poly.send (name z).val (f z)

omit [Fintype V] in
theorem input (f:Z→ℂ):fold J name (lambda (A) f)=entered J name f:=by
  simp only [lambda,entered,map_sum,single]

omit [Fintype V] [DecidableEq Z] in
theorem vacant (f:Z→ℂ):(entered J name f).part J.quiet=0:=by
  rw [entered,Poly.part_sum]
  exact Finset.sum_eq_zero fun z _=>part_quiet_hot (name z) (f z)

theorem ordinary (f:Z→ℂ):fold J name (Poly.pass (lambda (A) f))=Poly.pass (entered J name f):=by
  rw [pass_map _ _ (lambda_quiet _) (by rw [input,vacant]),input]

variable {G:Gauge}{n:Side}

theorem original (P:Rep G n)(row:Z→Pulse G n)(U:Config G n):
    fold J name (polar P (A) row U)=
      composeAt P U (entered J name (fun z=>(row z).1 U))
        (fun K=>entered J name (fun z=>(row z).2 K U)):=by
  unfold polar
  rw [maps_at _ _ _ _ (lambda_quiet _) (by rw [input,vacant])]
  simp only [input]

end YM.Integration.WilsonReceivedDepositedAlias

