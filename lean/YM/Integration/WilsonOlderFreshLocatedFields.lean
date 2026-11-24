import YM.Integration.WilsonOlderFreshLocatedPayment
import YM.Integration.WilsonOlderFreshLocatedSource
import YM.Integration.WilsonOlderFreshLocatedBook

/-! The exact two premise families used by LocatedFunded, on the true
located group words and all retained lags. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOlderFreshLocatedFields
open Filter MeasureTheory Lattice Wilson RG Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FormalBulk08 City Pose
open WilsonTrueProjectedLocatedBasis WilsonTrueProjectedLocatedHistory Pert.Asymptotics
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){d D N per b j:ℕ}
local notation "axes" => Letter (R.family.labels.level d)
local notation "side" i:max => R.family.side i per

local notation "g₀" => ConnectedActivityE6.Coat.gStep (R.family.path.rep N per j).beta

def Event (wood:Primer.Families R.family)(a:hue G)(depth:d<D)(digit:∀i,Site (R.family.S.block i))(Q:ℕ)
    (t:Fin (Q+1))(w:axes)(V:Config G (side (j+1)) → ℝ)(W:Rep G (side j))(o:Site (side j))
    (upper:Config G (side (j+1)) → ℂ)(book:axes → Config G (side j) → ℂ)(cost:ℝ):Prop:=
  Integrable (fun U=>(V U:ℂ)*upper U) (prior G _) ∧
  ∃z:store R.family d per j,Paid R W o z cost ∧
    transition (C:=R.family) d N per j (film V upper g₀ t.val)=
      film W.eval (nextWord R wood a depth digit N j Q g₀ book t w) g₀ t.val+z.density o (R.family.localSection d) W

theorem reprice (wood:Primer.Families R.family)(a:hue G)(depth:d<D)(digit:∀i,Site (R.family.S.block i))(Q:ℕ)
    (t:Fin (Q+1))(w:axes)(V:Config G (side (j+1)) → ℝ)(W:Rep G (side j))(o:Site (side j))
    (upper:Config G (side (j+1)) → ℂ)(lower:axes → Config G (side j) → ℂ)
    {U:Config G (side (j+1)) → ℂ}{L:axes → Config G (side j) → ℂ}{x y:ℝ}
    (incoming:upper=U)(outgoing:lower=L)(bill:x≤y)
    (paid:Event (N:=N) R wood a depth digit Q t w V W o U L x):
    Event (N:=N) R wood a depth digit Q t w V W o upper lower y:=by
  subst U L
  obtain ⟨ok,z,h,field⟩:=paid
  exact ⟨ok,z,WilsonOlderFreshLocatedPayment.enlarge R h bill,field⟩

end YM.Integration.WilsonOlderFreshLocatedFields
end
