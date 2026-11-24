import YM.Integration.WilsonOriginalMountedRegular

/-! The largest amount needed on a subface is paid using only the finite set of
original names on the requested face. All four norm bounds come from actual site hits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusMount
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder ConnectedActivityE6
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.AbsoluteSums Push.AbsoluteSums.Animals
open WilsonRootedKioskOccupiedSlip WilsonOriginalOrdinaryFlatHulls
open WilsonOriginalSeparatedRegular WilsonOriginalSeparatedMask Comparison.Density.Transport Multi
open scoped BigOperators Classical
variable {G:Gauge}{V:Type}[DecidableEq V]{J:Census V}

def aperture (w:V→ℝ)(s:J.Mode):ℝ:=∏v∈s.val,max 1 (w v)⁻¹

theorem positive (w:V→ℝ)(s:J.Mode):0 < aperture w s:=Finset.prod_pos fun _ _=>zero_lt_one.trans_le (le_max_left ..)

theorem sub (w:V→ℝ)(hp:∀v,0<w v){t s:J.Mode}(le:t.val⊆s.val):
    (Poly.toll w t)⁻¹ ≤ aperture w s:=by
  rw [Poly.toll,←Finset.prod_inv_distrib]
  apply le_trans (Finset.prod_le_prod (fun v _=>inv_nonneg.mpr (hp v).le) (fun v _=>le_max_right 1 (w v)⁻¹))
  exact Finset.prod_le_prod_of_subset_of_one_le le (fun _ _=>zero_le_one.trans (le_max_left ..))
    (fun _ _ _=>le_max_left ..)

variable {n:Side}{p:BudgetPoint}{o:V→Site n}{I X:Type}(L:Lamps X I G p o J)
theorem paid_nn {w:V→ℝ}{a c:ℝ}(b:L.Paid w p.B a c):0 ≤ c:=by
  obtain ⟨_,_,_,hit⟩:=b.budget
  exact budget_nonneg (hit 0)
theorem gross_nn {w:V→ℝ}{a c:ℝ}(b:Gross L w p.B a c):0 ≤ c:=by
  obtain ⟨_,_,_,hit⟩:=b.before
  exact budget_nonneg (hit 0)

variable {i per:ℕ} [Fintype V]
def join (R:Run G) (vac:RG.Rep G (R.family.side i per))
    (row:WilsonOriginalOccupiedWindow.Slice R J vac)
    (lower:Config G (R.family.side i per) → Poly J)(s:J.Mode)
    {X X' I Iold I':Type}[Countable I][Countable Iold][Countable I']
    {o o':V→Site (R.family.side i per)}{b:BudgetPoint}
    (L:Lamps X I G vac.p o J)(old:Lamps X Iold G vac.p o J)(next:Lamps X' I' G b o' J)
    (x:X)(z:X') (registered:∀U,row.A.E.log row.x U=(L.join old).log x U)
    (physical:∀U,lower U=(vac.eval U:ℂ) • Poly.pass (bare next z U))
    {w w':V→ℝ}(hw:∀v,0 < w v)(hw':∀v,0 < w' v){α α' regular gross rent nextGross:ℝ}
    (width:0 ≤ α)(width':0 ≤ α')(paid:L.Paid w vac.p.B α regular)
    (refund:old.Paid w vac.p.B α rent)(stock:Gross L w vac.p.B α gross)
    (other:Gross next w' b.B α' nextGross)
    (h:ℕ)(tube:LinkTube G)(front:Hot J→V)(mem:∀t,front t∈t.val.val)
    (words:∀t:Hot J,t.val.val⊆s.val→Row vac.p tube (o (front t))
      (fun U=>(bare L x U).part t.val) (fun U=>(bare next z U).part t.val))
    {δ:ℝ}(delta:0 ≤ δ)(due:∀t ht,(words t ht).price ≤ δ):WilsonOriginalMountedRegular.Filing R vac row lower s where
  X:=X
  X':=X'
  I:=I
  Iold:=Iold
  I':=I'
  o:=o
  o':=o'
  nextBudget:=b
  L:=L
  old:=old
  next:=next
  x:=x
  z:=z
  mounted:=registered
  declared:=physical
  w:=w
  w':=w'
  hw:=hw
  hw':=hw'
  α:=α
  α':=α'
  regular:=regular
  gross:=gross
  rent:=rent
  nextGross:=nextGross
  width:=width
  nextWidth:=width'
  paid:=paid
  refund:=refund
  stock:=stock
  other:=other
  regular_nn:=paid_nn L paid
  gross_nn:=gross_nn L stock
  rent_nn:=paid_nn old refund
  other_nn:=gross_nn next other
  W:=aperture w s
  W':=aperture w' s
  M:=max (aperture w s*(regular+rent)) (aperture w' s*nextGross)
  δ:=δ
  wallet_nn:=(positive w s).le
  M_nn:=(mul_nonneg (positive w s).le (add_nonneg (paid_nn L paid) (paid_nn old refund))).trans (le_max_left ..)
  delta_nn:=delta
  source:=fun _ e=>sub w hw e
  target:=fun _ e=>sub w' hw' e
  amount:=⟨le_max_left ..,le_max_right ..⟩
  h:=h
  tube:=tube
  front:=front
  mem:=mem
  words:=words
  due:=due

end YM.Integration.WilsonOriginalCensusMount
end
