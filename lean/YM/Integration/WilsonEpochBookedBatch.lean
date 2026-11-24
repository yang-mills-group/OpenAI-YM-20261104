import YM.FVA2.Main
import YM.Integration.WilsonEpochPositionCoefficients

/-! Booking the finite, source-resolved comparison into the original point
and smeared arrays. The prescribed MS and OPE tables use this very same
epoch. The finite numerical error still consists of specified signed Wilson
stencil insertions on that regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEpochBookedBatch

open Function Lattice XSpace XSpace.Cirrus XSpace.Structure1 XSpace.Normalize
open FVA2 FVA2.Arrival FVA2.Register MS MS.Land
open WilsonEpochPositionCoefficients
open scoped BigOperators Classical

variable {G : Gauge} (R : PhysicalNext.Repeat.Legato.Run G)
variable (N : WilsonPrescription G) (i n d k : ℕ)
variable (a : Test n) (p : Tags G d n)
private abbrev source (G : Gauge) := List (Folio G) → PowerSeries ℝ

def atPoint (s : source G) (t : Fin n → Dframe.Toon G d) (x : Fin n → Cover) :
    PowerSeries ℂ :=
  Dframe.Csum (N.run.step i) (fun j => (t j).size) •
    PowerSeries.map Complex.ofRealHom (Birth.scan (Handoff.wordSymbols n t x) s)

def atBatch (s : source G) (t : Fin n → Dframe.Toon G d) : PowerSeries ℂ :=
  ((N.run.step i).spacing : ℂ)^(4*n) •
    ∑ x : Fin n → (N.run.step i).Sites, (N.run.step i).smear (lift ∘ x) a •
      atPoint N i n d s t (lift ∘ x)

private abbrev field := actual R N.scheme (N.run.step i).p.side
private abbrev change := residual R N.scheme (N.run.step i).p.side
variable {i n d k}

theorem point {B : ℕ} (P : Handoff.Directory N i B) (t : Fin n → Dframe.Toon G d)
    (x : Fin n → Cover) (h : Handoff.Directory.budget G n d + k ≤ B) :
    PowerSeries.coeff k (atPoint N i n d (field R N i) t x) =
      PowerSeries.coeff k (P.point_fk n d t x) +
      PowerSeries.coeff k (atPoint N i n d (change R N i) t x) := by
  have he := epoch R N i B P (Handoff.wordSymbols n t x) k
    ((Nat.add_le_add_right (Handoff.Directory.cost n d t x) k).trans h)
  have sum := sub_eq_iff_eq_add.mp he
  simp only [atPoint,Handoff.Directory.point_fk,map_smul,PowerSeries.coeff_map,
    smul_eq_mul]
  rw [sum,map_add,mul_add,add_comm]

theorem batch {B : ℕ} (P : Handoff.Directory N i B) (t : Fin n → Dframe.Toon G d)
    (h : Handoff.Directory.budget G n d + k ≤ B) :
    PowerSeries.coeff k (atBatch N i n d a (field R N i) t) =
      PowerSeries.coeff k (P.sweep_fk n d a t) +
      PowerSeries.coeff k (atBatch N i n d a (change R N i) t) := by
  simp only [atBatch,Handoff.Directory.sweep_fk,map_smul,map_sum]
  simp_rw [point R N P t (lift ∘ _) h,smul_add,Finset.sum_add_distrib]
  exact smul_add _ _ _

/-- Both complete incoming test arrays, including arbitrary phases in the
multilinear input, with the actual discrepancy before any absolute values.
The same Match supplies the formal separated OPE in the same prescription. -/
theorem booked {hG : G.Simple}
    {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {S : Prescription (Press.portDeck G)} {dial : Bool}
    (M : Main.Match N hG T S dial) (i B n d k : ℕ)
    (P : Handoff.Directory N i B) (h : Handoff.Directory.budget G n d + k ≤ B)
    (x : Fin n → Cover) (a : Test n) (p : Tags G d n) (ν : ℝ) :
    ((∑ t : Fin n → Dframe.Toon G d, Dframe.each t p *
      PowerSeries.coeff k (atPoint N i n d (field R N i) t x)) -
      litP N.scheme d (N.run.step i) (wrap (N.run.step i).p.side ∘ x) k p =
     ∑ t : Fin n → Dframe.Toon G d, Dframe.each t p *
      PowerSeries.coeff k (atPoint N i n d (change R N i) t x)) ∧
    ((∑ t : Fin n → Dframe.Toon G d, Dframe.each t p *
      PowerSeries.coeff k (atBatch N i n d a (field R N i) t)) -
      XSpace.Normalize.batch N.scheme (N.run.step i) d k n a p =
     ∑ t : Fin n → Dframe.Toon G d, Dframe.each t p *
      PowerSeries.coeff k (atBatch N i n d a (change R N i) t)) ∧
    O.Canon.Supplied N T ν := by
  obtain ⟨qp,qb⟩ := M.batchFromEpochFk i B P d k n x a p h
  refine ⟨?_,?_,M.separatedOPE ν⟩
  · rw [qp]
    simp_rw [point R N P _ x h,mul_add,Finset.sum_add_distrib,add_sub_cancel_left]
  · rw [qb]
    simp_rw [batch R N a P _ h,mul_add,Finset.sum_add_distrib,add_sub_cancel_left]

end YM.Integration.WilsonEpochBookedBatch
end

