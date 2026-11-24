import YM.Integration.WilsonPhysicalThermalWickStretched
import YM.Integration.WilsonPhysicalThermalWickSky

/-! The physical count-dependent enlargement has no charge at the free
ordinary table. The covariance used here is precisely the filed Maxwell
one on the original two true, separated positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickFree
open Lattice Wilson RG Labels Function Filter
open Next.Rank Next.Rank.Atlas Next.Rank.Station Next.Rank.Perch Next.Rank.Glimmer
open Next.Rank.Prayer Next.Rank.Beamer Next.Rank.Configuration Next.Rank.Common Next.Rank.Normal
open Marker Glyph Exponential Cells
open WilsonPhysicalThermalWickSky (labels)
open WilsonPhysicalThermalWickRescale (pure)
open scoped BigOperators Classical Topology
variable {G:Gauge}{C:Family G}{d0:Fin 2→ℕ}{d:ℕ}
theorem original (x:Points 2)(hx:x∈conf 2)(v:(i:Fin 2)→C.label (d0 i))(hY:∀i,d0 i≤d)
    (q:Fin 2→ℕ)(ranks:∀i,pure (q i) (thawKey (labels v hY i)))(P:ℝ):
    let a:=WilsonPhysicalThermalWickStretched.rates (P^(q 1-q 0))
    Read.maxProfile C x (jointX (WilsonReporterWeightedOrdinary.stretch C a v))=
      Read.maxProfile C x (jointX v):=by
  dsimp only
  funext S
  change (Read.maxProfile _ _ _).part S=(Read.maxProfile _ _ _).part S
  rw [WilsonPhysicalThermalWickStretched.charge,WilsonPhysicalThermalWickStretched.mask]
  by_cases hi:1∈S.val
  · rw [if_pos hi]
    by_cases diff:q 0<q 1
    · have clear:(Read.maxProfile C x (jointX v)).part S=0:=
        (stagesX v hY x hx S).trans ((Configuration.G_subset hx (labels v hY) S).trans
          (WilsonPhysicalThermalWickFaces.zero q diff _ ranks (currentX hx G d)
            (WilsonPhysicalThermalWickReturned.within hx) S.val hi))
      rw [clear,mul_zero]
    · simp [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt diff)]
  · rw [if_neg hi,one_mul]

end YM.Integration.WilsonPhysicalThermalWickFree
end
