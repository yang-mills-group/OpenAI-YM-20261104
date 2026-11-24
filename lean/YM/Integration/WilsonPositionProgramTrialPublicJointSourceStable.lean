import YM.Integration.WilsonPositionProgramTrialPublicJointSourceExchange

/-! The signed difference of two actually entered sources with the same projected return. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointSourceStable
open Function Finset Matrix Lattice Wilson RG Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel.Mark
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonPositionProgramTrialPublicJointSourceExchange (change carried)
open scoped BigOperators Classical

variable {G:Gauge}{h D k u e:ℕ}{F:Frame G h}{H:Hol G}{J:SectionData F}{fit:h<D}
variable {w:Rails h k u e}{E W B V:Credit}(X:CutsP H J fit w E W B V)

theorem empty (L:Levels G)(O:ChartRatio G)(N m i:ℕ):
    street L O J fit N m i (0:Verse F)=0:=by
  have z:music (relativeF L O N m i) (0:Verse F)=0:=by
    funext j
    exact map_zero _
  rw [street,z,Matrix.mulVec_zero]

def seen (P:TowerS G D):Verse F:=
  opal F (spools X.ax X.tx X.ceilC k h X.m X.i P)

theorem difference (P Q:TowerS G D)(p:On k P)(q:On k Q):
    seen X (P-Q)=seen X P-seen X Q:=by
  let g:=X.L.L.V.hG
  let z:=X.L.L.V.green
  have upto:X.m+X.i ≤ X.ceilC:=le_rfl
  unfold seen
  rw [spool_sub upto g z p q,On.read_sub F (spoolEnd upto g z p) (spoolEnd upto g z q)]

theorem original:
    ∃C:Credit,∀(P Q:TowerS G D)(A B':ℝ),On k P → On k Q → 0 ≤ A → 0 ≤ B' →
      (∀j r,j ≤ e → Fruit 0 1 u (P.2 j r) A) → (∀j r,j ≤ e → Fruit 0 1 u (Q.2 j r) B') →
      seen X P=seen X Q →
      ∃Y:CutsP H J fit w E W B V,
        Y.L=X.L ∧ Y.L'=X.L' ∧ Y.m=X.m ∧ Y.i=X.i ∧ Y.N=X.ceilC ∧
        Y.pt=P-Q ∧ Y.fuel=A+B' ∧ Y.tileP=0 ∧ P-Q=Y.springP Y.i ∧
        (∀j<X.i,Spout X.ax X.tx X.ceilC (X.m+j) h k (Y.springP (j+1))=Y.springP j) ∧
        ∀t ≤ e,∀j ≤ X.i,∀r,Fruit 0 1 u ((Y.springP j).2 t r)
          (C.buy Y.Age*Real.exp (-(X.ax.S.scale X.ceilC-X.ax.S.scale (X.m+j))/4)*(A+B')):=by
  obtain ⟨C,paid⟩:=WilsonIndependentMatchedKernelResidual.original H J fit w E W B V
  refine ⟨C,?_⟩
  intro P Q A B' p q a b pfee qfee agree
  have legal:=p.diff q
  have upto:X.m+X.i ≤ X.ceilC:=le_rfl
  let Y:=WilsonIndependentMatchedKernelResidual.diagonal X.L X.L' X.he X.m X.i X.ceilC
    X.ha upto (P-Q) legal (A+B') (add_nonneg a b) (fun j r touch=>(pfee j r touch).diff (qfee j r touch) zero_le_one)
  have z:seen X (P-Q)=0:=by rw [difference X P Q p q,agree,sub_self]
  have home:=TallOracle X.L X.ha upto (P-Q) legal
  have tile:Y.tileP=0:=by
    apply street_up X.L.L X.ha upto
    change street X.ax X.tx J fit X.ceilC X.m X.i Y.tileP=_
    rw [←show seen X (P-Q)=street X.ax X.tx J fit X.ceilC X.m X.i Y.tileP from home,z,empty]
  have pure:=Y.carve1
  rw [tile,Shrine_zero,sub_zero] at pure
  refine ⟨Y,rfl,rfl,rfl,rfl,rfl,rfl,rfl,tile,pure.symm,fun j hj=>Y.carve2 hj,?_⟩
  exact (paid Y).2.2

end YM.Integration.WilsonPositionProgramTrialPublicJointSourceStable
