import YM.Integration.WilsonPhysicalThermalWickLabels
import YM.MergeProof.West.Teddy

/-! Original field-count support gives the degree of the complete two-label
ordinary polynomial on each chosen proper face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickDegree
open MvPolynomial Next.Rank Next.Rank.Normal
open WilsonPhysicalThermalWickRescale (pure)
open scoped Classical BigOperators
universe u
variable {V:Type u}

theorem single (q:ℕ)(p:poly V)(rank:pure q p):p.totalDegree≤q:=by
  apply Finset.sup_le
  intro m hm
  rw [←rank m hm]
  simp [Finsupp.weight_apply,Finsupp.sum]

open private ceiling from YM.MergeProof.West.Teddy in
theorem original (q:Fin 2→ℕ)(p:Fin 2→poly V)(ranks:∀i,pure (q i) (p i))
    (d:ℕ)(hd:∀i,q i≤d)(S:Finset (Fin 2)):(pot S p).totalDegree≤2*d:=
  ceiling S p (fun i=>(single _ _ (ranks i)).trans (hd i))

end YM.Integration.WilsonPhysicalThermalWickDegree
end
