import YM.Integration.WilsonReceivedDepositedOrbitalSlice

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalMonomials
open Finset Marker Multi Comparison.RG02 Comparison.RG02.Order
open WilsonReceivedDepositedOrbitalSlice
open scoped Classical BigOperators
variable {V W Z:Type}[Fintype V][DecidableEq V][Fintype W][DecidableEq W][Fintype Z][DecidableEq Z]
  {A:Census V}{J:Census W}{r:ℕ}

theorem left (F:Poly A →ₐ[ℂ] Poly J)(x:Poly A):
    hom F r (Join.injectLeft A (indices r) x)=Join.injectLeft J (indices r) (F x):=by
  apply Join.both_parts
  intro s t
  have term:slice (Join.injectLeft A (indices r) x) t=if t=(indices r).quiet then x else 0:=by
    apply Marker.Poly.ext
    intro v
    change (Join.injectLeft A (indices r) x).part (Join.pair v t)=_
    rw [Join.left_part]
    by_cases empty:t=(indices r).quiet <;> simp [empty]
  rw [show (hom F r (Join.injectLeft A (indices r) x)).part (Join.pair s t)=_ from at_pair F _ s t,
    term,Join.left_part]
  by_cases empty:t=(indices r).quiet <;> simp [empty]

theorem right (F:Poly A →ₐ[ℂ] Poly J)(w:Poly (indices r)):
    hom F r (Join.injectRight A (indices r) w)=Join.injectRight J (indices r) w:=by
  apply Join.both_parts
  intro s t
  have term:slice (Join.injectRight A (indices r) w) t=algebraMap ℂ (Poly A) (w.part t):=by
    apply Marker.Poly.ext
    intro v
    change (Join.injectRight A (indices r) w).part (Join.pair v t)=(Poly.send A.quiet (w.part t)).part v
    rw [Join.right_part,Poly.part_send]
  rw [show (hom F r (Join.injectRight A (indices r) w)).part (Join.pair s t)=_ from at_pair F _ s t,
    term,F.commutes,Join.right_part]
  exact Poly.part_send ..

/-- Each previously deposited connected word carries its entire thermal polynomial.
    The unmarked polynomial is shared by every occupied contribution. -/
def source (J:Census V)(name:Z→J.Mode)(quiet:Poly (indices r))(word:Z→Poly (indices r)):Grade J r:=
  Join.injectRight J _ quiet+∑z,Join.injectLeft J _ (Poly.send (name z) 1)*Join.injectRight J _ (word z)

variable (J:Census V)(name:Z→Hot J)

theorem relabel (quiet:Poly (indices r))(word:Z→Poly (indices r)):
    hom (WilsonReceivedDepositedAlias.fold J name) r
      (source (Stock.census Z) ((Stock.census Z).fire) quiet word)=
      source J (fun z=>(name z).val) quiet word:=by
  simp only [source,map_add,map_sum,map_mul,left,right,WilsonReceivedDepositedAlias.single]

omit [DecidableEq Z] in
theorem coefficient (J:Census V)(name:Z→J.Mode)(quiet:Poly (indices r))(word:Z→Poly (indices r))
    (s:J.Mode)(t:Index r):
    (source J name quiet word).part (Join.pair s t)=
      (if s=J.quiet then quiet.part t else 0)+∑z,if s=name z then (word z).part t else 0:=by
  simp only [source,Poly.part_plus,Join.right_part,Poly.part_sum,Join.separate,Poly.part_send]
  congr 1
  refine Finset.sum_congr rfl fun z _=>?_
  by_cases belongs:s=name z <;> simp [belongs]

end YM.Integration.WilsonReceivedDepositedOrbitalMonomials
end
