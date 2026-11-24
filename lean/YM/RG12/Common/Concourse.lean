import YM.RG12.Common.Advance
import YM.RG12.Arche.Moor
/-!
# Assemble on the construction selecting exact k readers, all levels after a short hit
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Commission
open Function Filter Set Lattice Wilson RG RG.Supply Next.Rank Next.Rank.Tapes Next.Rank.Perch Next.Rank.Station Real Asymptotics Ship Peak
open PhysicalNext PhysicalNext.RankCovariance PhysicalNext.InteractingRank.Soft
open MergeProof MergeProof.East Next.Rank.Tapes.West MergeProof.Accent
open Pert.Dense
open Precision
open scoped Topology BigOperators
variable {G:Gauge}{p:Sheet G}{w:Rolls p}{θ:Protection w}{D:Delays θ}{B:Bar D}
variable (M: MapPrices) (O:HaarBudget G)(J:ChartRatio G)
variable (W:Wait B)(U:StationPort W M O J)
variable {Q:Wait B}
-- A prescription of stations from SAME binding for all d. Bound path relations between k
-- and latest eligible; preserved orientation and arity chart in Poised.
structure Port (C:Family G) where
   rate :ℕ→ℕ
   panels : ∀ d,Fin 3→ Tapes.Panel d
   budget : ℕ→ℝ
   haar : HaarBudget G
   locality : ChartRatio G
   chart : Binding C

variable {C:Family G}
def Covered (P:Port C)(h:C.Makes) : Prop :=
  Tendsto P.rate atTop atTop ∧ (∀ d i,i ≤ d → MergeProof.Accent.generator G i≤ P.budget d) ∧ ∀ d, ∀ᶠ k:ℕ in atTop,
    let j:= P.rate k
    j ≤ k ∧ (C.S.a j)/(C.S.a k) ≤ C.path.levels.clock.hatBeta k ∧ ∃ T,Poised (P.panels d) P.chart h P.haar P.locality (trays d) (P.budget d) j T
include U
lemma staff (h:U.Certified) {a:Levels G}(hW:Paid W a) (g:ℕ→ℕ) (hg:Tendsto g atTop atTop) (he: ∀ᶠ k:ℕ in atTop,
  g k ≤ k ∧ Interior W a (g k) ∧ (a.S.a (g k))/(a.S.a k) ≤ a.clock.hatBeta k) (hC:C.Makes)(x:Binding C)(hK:x.prices=M)(hA: a=C.path.levels) (hG:Next.Rank.East.ParadeX C): ∃ P:Port C,Covered P hC:=by
    subst a
    refine ⟨⟨g,U.panels,U.cost,O,J,x⟩,hg,h.reasonable,fun d=> ?_⟩
    have hx:= hg.eventually (h.orders C hW x hK hC hG d)
    filter_upwards [he,hx] with k hk hx using ⟨hk.1,hk.2.2,hx hk.2.1⟩
end YM.RG12.Commission
