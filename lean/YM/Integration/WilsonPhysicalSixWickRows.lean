import YM.Integration.WilsonPhysicalCentralProgram
import YM.Integration.WilsonMaxwellThermometerChargedHeads
import YM.WilsonCoeffUV.Wick.Unipotent

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalSixWickRows
open Filter Function Labels Lattice RG Source Wilson WilsonCoeffUV WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Soil WilsonCoeffUV.Bank
open WilsonCoeffUV.Power WilsonCoeffUV.Bank.Carp Matrix
open scoped BigOperators Classical
variable {G:Gauge} {h D e:ℕ} {F:Frame G h}

theorem arity (F:Frame G h) (i:Alma F):2*valence F i≤weave F i:=
  WilsonMaxwellThermometerChargedHeads.graded F (sheet F i)

theorem two {P:Gen (Vote D) (YForest G)} {r:ℕ} (A:Levels G) (N m k:ℕ)
    (slots:still P (r+2)):paveS A m N k P r=P r:=by
  unfold paveS mason
  rw [Finset.sum_apply,Finset.sum_eq_single_of_mem 0]
  · rfl
  · simp
  intro i _ hi
  exact ice_none slots (by omega)

theorem retained (cap:h≤6) (X:Island F D) (filed:Shimmer X) (A:Levels G) (m N:ℕ)
    (i:Alma F) (nonlinear:2≤valence F i) (j:Alma F):
    wickM A m N F X.2 i j=(1:Wall F) i j:=by
  have rank:=arity F j
  have bound:=F.bound (sheet F j)
  change weave F j≤h at bound
  have seats:still (X.2 j 0) (valence F i+2):=by
    intro l hl
    exact (streams filed j).born 0 l (by omega)
  unfold wickM wickT
  rw [Matrix.of_apply,two A N m h seats,←g_lone,epoch filed j 0 i,Matrix.one_apply]
  simp [eq_comm]

variable {H:Hol G}{T:SectionData F}{cut:h<D}{E W:Credit}
theorem original (L:Theatre H T cut e E W) (cap:h≤6) {m N:ℕ} (top:m≤N)
    (book:L.V.anchor≤ m) (i:Alma F) (nonlinear:2≤valence F i) (x:Alma F→ℝ):
    (Wray L.V.draws L.V.paid T cut N m *ᵥ x) i=x i:=by
  change ∑ j:Alma F,wickM L.V.draws m N F (L.lore N m).2 i j*x j=_
  simp_rw [retained cap (L.lore N m) (production L top book).1 L.V.draws m N i nonlinear]
  simp [Matrix.one_apply,ite_mul]

theorem nonunit (L:Theatre H T cut e E W) (cap:h≤6) (simple:G.Simple) {m N:ℕ}
    (top:m≤N) (book:L.V.anchor≤ m) (i:Alma F) (live:sheet F i≠0) (x:Alma F→ℝ):
    (Wray L.V.draws L.V.paid T cut N m *ᵥ x) i=x i:=by
  have pos:0<valence F i:=F.factors_pos (sheet F i) live
  have two:valence F i≠1:=WilsonMaxwellThermometerWardColors.arity simple F (sheet F i)
  exact original L cap top book i (by omega) x

end YM.Integration.WilsonPhysicalSixWickRows
