import YM.Integration.WilsonPhysicalThermalWickRescale
import YM.Next.RANK.LegBlock
import YM.Next.RANK.Prepaid

/-! Count homogeneity of the actual cut jet variables, including quotient
nulls and the scalar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickLabels
open Lattice Wilson RG Labels Function MvPolynomial Next.Rank Next.Rank.Configuration
open WilsonPhysicalThermalWickRescale
open scoped BigOperators Classical
variable {G:Gauge}{d D:ℕ}

private theorem counts (m:KeyIn G d→₀ℕ):
    (Finsupp.weight bidegree (Finsupp.mapDomain (Subtype.val :KeyIn G d→Key G) m)).2=
      Finsupp.weight (fun _:KeyIn G d=>1:KeyIn G d→ℕ) m:=by
  induction m using Finsupp.induction_linear with
  | zero=>simp
  | add a b ha hb=>simp [Finsupp.mapDomain_add,ha,hb]
  | single i b=>simp [Finsupp.weight_apply,bidegree]

theorem filed (v:Label G d)(w q:ℕ)(source:pureDegree v.val w q):
    pure q (thawKey v):=by
  intro m hm
  have entry:=coeff_rename_mapDomain (Subtype.val :KeyIn G d→Key G) Subtype.val_injective (thawKey v) m
  rw [returns] at entry
  have paid:=source (show coeff (Finsupp.mapDomain (Subtype.val :KeyIn G d→Key G) m) v.val≠0 by
    rw [entry]; exact mem_support_iff.mp hm)
  exact (counts m).symm.trans (congrArg Prod.snd paid)

theorem axis (F:Frame G d)(i:F.Index)(raises:d≤D):
    pure (F.grades i).2 (thawKey (raiseLabel G raises (F.basis i))):=by
  apply filed _ (F.grades i).1
  exact (pure_grade (F.grades i) (F.basis i)).mp (F.pure i)

end YM.Integration.WilsonPhysicalThermalWickLabels
end
