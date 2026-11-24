import YM.Integration.WilsonMarkedIndependentChargedFoldedIntegral

/-! Attach the original per-stencil ticket to a unary charged source and its literal lifted site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFoldedSourceTicket
open Function Filter Finset Lattice Wilson RG Source Labels Marker Multi Precision Tree
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Winding WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Classical BigOperators

variable {G:Gauge}{V:Type}[DecidableEq V][Fintype V][Subsingleton V]{D k:V→ℕ}
  {I:V→Type}[∀i,Fintype (I i)](X:∀i,I i→Seed G (D i))(s:V)(a:I s)

def picked (i:V)(_ :Unit):Seed G (D i):=(Subsingleton.elim s i) ▸ X s a

omit [DecidableEq V] [Fintype V] [∀i,Fintype (I i)] in
theorem array (z:Unit):picked X s a s z=X s a:=rfl

omit [DecidableEq V] [∀i,Fintype (I i)] in
theorem ledger (cap:ℕ)(w:ℝ):
    bill (picked X s a) k cap w=charge X k cap w s a:=by
  unfold bill
  rw [Finset.sum_eq_single s]
  · simp only [Fintype.sum_unique]
    rfl
  · intro j _ hj
    exact (hj (Subsingleton.elim j s)).elim
  · simp

omit [DecidableEq V] [Fintype V] [∀i,Fintype (I i)] in
theorem legal (h:(X s a).rank ≤ k s+(X s a).head):
    ∀i b,(picked X s a i b).rank ≤ k i+(picked X s a i b).head:=by
  intro i b
  cases Subsingleton.elim s i
  exact h

omit [∀i,Fintype (I i)] in
theorem material (z:V → Cover)(test:Case D):
    tuftV (touch test {s}) (independent (picked X s a) z {s})=
      let A:=X s a
      tuftV (touch test {s}) (OriginalMarkedSourceComet.source D s
        (colour A.path A.color A.weight A.quadrant) A.knob A.point A.head (z s)):=by
  rw [IndependentSourcePathFamily.singleton, IndependentSourcePathFamily.single, Fintype.sum_unique]
  rfl

variable (P:Patch)(y:V → Cover)
def root (i:V):Cover:=fun e=>((y i e)-(lift (wrap P.L (y i))) e)/(P.L.val:ℤ)
def cell (i:V):Site P.L:=wrap P.L (y i)

omit [DecidableEq V] [Fintype V] [Subsingleton V] in
theorem placed (i:V):chartIn P (root P y) (cell P y) i=y i:=by
  funext axis
  have eqv:wrap P.L (lift (wrap P.L (y i)))=wrap P.L (y i):=wrap_lift _
  have div:(P.L.val:ℤ)∣(y i axis)-(lift (wrap P.L (y i))) axis:=
    (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp (congrFun eqv axis)
  change (P.L.val:ℤ)*(((y i axis)-(lift (wrap P.L (y i))) axis)/(P.L.val:ℤ))+
    (lift (wrap P.L (y i))) axis=y i axis
  rw [mul_comm,Int.ediv_mul_cancel div]
  abel

end YM.Integration.WilsonOriginalFoldedSourceTicket
