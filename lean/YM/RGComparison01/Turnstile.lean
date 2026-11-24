import YM.PCalc.Band

/-!
# Domain adapter for local analytic estimates

 We do *not* want a permission to move or `retain` in the scanning
 of the actual witness' history when weighing other faithful
 REPRESENTATIONS of its actual densities. Having changed a β outside the
 allowed changes of representation of such permissions and then corrected
 using signed eNatural, such a permission in general would be unavailable.
 Instead, state/use estimates sensitive only to the real Roll, SR paths,
 levels & REP data. `relieve` uses **all numerics** from the same `B`;
 it forgets the `retain` predicate. It's NOT a witness and not building
 another path for any Conv/Move principle.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function RG Lattice Wilson RG.Shoot RG.Supply Input Precision
variable {G:Gauge}{s: Sheet G}{D:Rolls s}{Θ:Protection D}{W:Delays Θ}{Y:Bar W}{I:Wait Y}
  {Z:ChartRatio G}{K:MapPrices}{P:PostCost D}

def relieve (B:Directed G I Z K P): Directed G I Z K P:= { B with
   bake:= { B.bake with retain:= fun _ _ _ _=> True } }
-- statement clearer for consumer of authentic path alignment
abbrev Travels (B:Directed G I Z K P)(N m p:ℕ)(R:Rep G (B.a.S.side m p)):= Lives (relieve B).bake N m p R
lemma visits {B:Directed G I Z K P}{N m n:ℕ}{R:Rep G (B.a.S.side m n)}(h:Lives B.bake N m n R): Travels B N m n R:= ⟨h.path,h.point,h.clip,h.valid,trivial⟩
end YM.RGComparison01
