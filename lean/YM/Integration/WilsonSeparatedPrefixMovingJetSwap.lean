import YM.Integration.WilsonSeparatedPrefixMovingJetOffice
import YM.WilsonCoeffUV.Product.Connected.Labels

/-! Match the native right-associated first-join roster to the AB deposit on
the actual Wilson stencils, using their finite fields and covered lifts. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonSeparatedPrefixMovingJetSwap
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power
open Embroider Precision Exterior Fountain Soil Gauge Source Source.Drops Labels WardBin Cosmos Bulb Realm PathCost Ore
open scoped BigOperators Classical
variable {G:Gauge}

private theorem full {i j:ℕ}{X Y:Era G ℝ}(hx:Auth i X)(hy:Auth j Y)(boards:∀n,X.1 n=Y.1 n):X=Y:=by
  have h:X.1=Y.1:=funext boards
  refine Prod.ext h ?_
  funext e r
  apply Bends.exten (hx.wing e r)
  rw [h]
  exact hy.wing e r


theorem original {h k:ℕ}{A B:Era G ℝ}(ha:Auth h A)(hb:Auth k B):agateV A B=agateV B A:=by
  apply full (ha.manor hb) (hb.manor ha)
  intro c
  let P:=A.1 c;let Q:=B.1 c
  have p:=ha.span c;have q:=hb.span c
  change woad P Q=woad Q P
  apply by_flash (woad_shell _ _ p q) (woad_shell _ _ q p) (woad_pure P Q) (woad_pure Q P)
  rw [woadap _ _ (finite_shell p) (finite_shell q),woadap _ _ (finite_shell q) (finite_shell p),mul_comm]
end YM.Integration.WilsonSeparatedPrefixMovingJetSwap
