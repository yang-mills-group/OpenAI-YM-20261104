import YM.Integration.WilsonIndependentNotebookMarkedEdge
import YM.WilsonCoeffUV.Product.Connected.Derive

/-! The ordinary product of two returned marked fields in the licensed
notebook coordinates. It uses every thermal and angular partition. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookOrdinaryProduct
open Function PowerSeries Lattice Laurent RG RegulatorIR RegulatorIR.Prim RegulatorIR.Diagram RegulatorIR.Ledger RegulatorIR.Oracle
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open WilsonIndependentConditionalNativeLinks (coarse)
open WilsonIndependentConditionalCoordinateHeat (orders ranks row)
open WilsonIndependentNotebookPayrollMark (source)
open WilsonIndependentSpoutFundedClocks (clock)
open scoped BigOperators Classical
variable {G:Gauge}{W:Type}{M:W→ℕ}(A:W→Levels G)(s:W→ℕ)

def product (X Y:Orders (Foot G)):Orders (Foot G):=
  orders (coarse G) (woad (orders (coarse G).symm X) (orders (coarse G).symm Y))

private theorem decoded (v:Page M)(P:Era G ℝ):orders (coarse G).symm (source A s v P)=
    mix (clock A (XSpace.Bare.chart G) s v) P.2:=by
  funext e r q
  apply congrArg (mix (clock A (XSpace.Bare.chart G) s v) P.2 e r)
  funext j
  exact (coarse G).apply_symm_apply (q j)

theorem restores (v:Page M){i j:ℕ}{P Q:Era G ℝ}(hp:Auth i P)(hq:Auth j Q):
    product (source A s v P) (source A s v Q)=source A s v (agateV P Q):=by
  unfold product
  rw [decoded,decoded]
  change orders _ _=orders _ (mix _ (woad P.2 Q.2))
  apply congrArg (orders (coarse G))
  let α:=clock A (XSpace.Bare.chart G) s v
  funext e r
  apply Bends.exten (Bends_woad (U:=Hooks G) (bend_mixX hp.wing α) (bend_mixX hq.wing α) e r)
  apply (bend_mixX (hp.manor hq).wing α e r).congr
  exact Filter.Eventually.of_forall fun n=>congrFun (congrFun
    (mix_wreath (P.1 n) (Q.1 n) α (hp.span n) (hq.span n)) e) r

theorem subtract (v:Page M)(P Q:Era G ℝ):
    source A s v (P-Q)=source A s v P-source A s v Q:=by
  change orders _ (mix _ (P.2-Q.2))=_
  rw [blend_woad]
  rfl

theorem preserves {p:ℕ}{X Y X' Y':Orders (Foot G)}(left:RegulatorIR.Clocks.Matches p X X')
    (right:RegulatorIR.Clocks.Matches p Y Y'):
    RegulatorIR.Clocks.Matches p (product X Y) (product X' Y'):=by
  intro e he
  apply congrArg (ranks (coarse G))
  unfold woad
  apply Finset.sum_congr rfl
  intro v hv
  have h:=Finset.HasAntidiagonal.mem_antidiagonal.mp hv
  change knitS (ranks _ (X v.1)) (ranks _ (Y v.2))=knitS (ranks _ (X' v.1)) (ranks _ (Y' v.2))
  rw [left v.1 (by omega),right v.2 (by omega)]

end YM.Integration.WilsonIndependentNotebookOrdinaryProduct
