import YM.Integration.WilsonMacroscopicRichIssuedCurrency
import YM.Integration.WilsonMacroscopicRichBookedLabels

/-! Every actual graded Wilson filing in the common capture experiment has the same full physical class to the earned precision. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichCaptureClass
open Filter Function Set Spec OPE OPE.Orbits PhysMS Cells Wilson Lattice
open RG16 RG16.Literal Trace.Physical.GermGraph FilteredWilsonProduct FilteredIntrinsicGramReadout
open RG MergeProof Bid
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable {I:Type}[Fintype I][Nonempty I]{d:I→ℕ}

def Filed (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower S){h top u:ℕ}(T:Stop C h top u)(v:(i:I)→(Climb.Bel C.book).Field (d i))
    (r:ℝ)(m N p b:ℕ)(x : I → Cover)(ub:u≤b)(bN:b≤N)
    (E rem:Grades d→ℝ)(z:Grades d→C.label h):Prop:=
  ∀g,∃Q,Funds C F.room.cutoff p N b h top u (E g) (rem g) (weight C h m)
    (WilsonReportingProductInvoice.source F R J v r m N p x g) T.live.1 ub bN (T.doors p) (z g) Q

theorem purchased (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower S)(leading:Leading F J)(fac:Facilities C f S)
    (pace:∀m,((C.S.block m).val:ℝ)≤Real.log (Lambda C.path.levels m))
    (h top u:ℕ)(T:Stop C h top u)(η M B:ℝ)(hη:0<η)(hM:0<M)(hB:20<B):
    ∃ E rem:Grades d→ℕ→ℝ,(∀g,RateIs atTop C.S.scale (E g) (-h) ∧ RateIs atTop C.S.scale (rem g) (-h)) ∧
    ∀ σ:ℝ,σ<1/8 → ∀ᶠ m:ℕ in atTop,
    let b:=port C (8*M) B (mul_pos (by norm_num) hM) m
    ∃ (ub : u ≤ b) (bm : b+1 < m),∀N p (hm : m < N)(ρ:ℝ)(x : I → Cover)(v:(i:I)→(Climb.Bel C.book).Field (d i)),
    Tuple C M η B m ρ x → (∀i,‖v i‖≤1) →
    let r:=C.S.a m*ρ
    let bN: b≤N :=(Nat.le_succ b).trans (bm.le.trans hm.le)
    let P:=Filed F R J T v r m N p b x ub bN (fun g=>E g m) (fun g=>rem g m)
    let Y:=field F R J v r m x (N,p)
    let label_u:=label (w:=(N,p)) F.room.cutoff (T.doors p) (ub.trans bN) Y
    (∃ z,P z) ∧ ∀z,P z → ‖S.project h label_u-S.project h (∑g,z g)‖≤
      Fintype.card (Grades d)*((C.S.a m)^h*Real.exp (-σ*C.S.scale m)):=by
  obtain ⟨E,rem,fiscal,dated⟩:=WilsonReportingProductInvoice.purchased (d:=d) F R J leading fac pace
    h top u T.live T.doors η M B hη hM hB
  obtain ⟨A,nn,fee⟩:=WilsonMacroscopicRichIssuedCurrency.field F.room.cutoff T.doors
  let π:=(S.project h).toContinuousLinearMap
  refine ⟨E,rem,fiscal,?_⟩
  intro σ sf
  have prices (g:Grades d):=WilsonMacroscopicRichIssuedCurrency.rate fac.simpleGate pace
    h u M B hM hB (E g) (fiscal g).1 (‖π‖*A) σ sf
  filter_upwards [dated,eventually_all.mpr prices] with m allCut price
  let b:=port C (8*M) B (mul_pos (by norm_num) hM) m
  obtain ⟨ub,bm,bank⟩:=allCut
  refine ⟨ub,bm,?_⟩
  intro N p hm ρ x v tuple cap
  obtain ⟨zr,record,_⟩:=bank N p hm ρ x v tuple cap
  refine ⟨⟨zr,record⟩,?_⟩
  intro z actual
  let Y (g:Grades d):=WilsonReportingProductInvoice.source F R J v (C.S.a m*ρ) m N p x g
  let bN:b≤N:=(Nat.le_succ b).trans (bm.le.trans hm.le)
  choose Q guild using actual
  have booked (g:Grades d):Booked C N p h (Y g) u (ub.trans bN):=(guild g).works u le_rfl ub
  have cont (g:Grades d):Continuous (Y g):=by
    change Continuous (∏ i, C.O N p (component F R J v g (C.S.a m*ρ) i) (location C.S m N p (x i)))
    rw [show (∏ i,C.O N p (component F R J v g (C.S.a m*ρ) i) (location C.S m N p (x i)))=fun U=>∏ i,C.O N p
      (component F R J v g (C.S.a m*ρ) i) (location C.S m N p (x i)) U from funext fun _=>Finset.prod_apply ..]
    exact continuous_finsetProd _ fun _ _=>C.continuousO ..
  have collect:=(IntrinsicProductLinearity.booked_sum C N p h u F.room.cutoff (T.doors p)
    (ub.trans bN) (fun _:Grades d=>(1:ℂ)) Y cont booked).2
  simp only [one_smul] at collect
  have exactField:field F R J v (C.S.a m*ρ) m x (N,p)=∑g,Y g:=by rw [field_expansion];rfl
  let y (g:Grades d):=label (w:=(N,p)) F.room.cutoff (T.doors p) (ub.trans bN) (Y g)
  have bound (g:Grades d):‖π (y g)-π (z g)‖≤(C.S.a m)^h*Real.exp (-σ*C.S.scale m):=by
    rw [←map_sub]
    have paid:=fee N p (ub.trans bN) (Y g) (z g) _ (guild g).currency
    exact (π.le_opNorm _).trans ((mul_le_mul_of_nonneg_left paid (norm_nonneg _)).trans
      (by rw [←mul_assoc];exact price g))
  unfold label
  rw [exactField,collect,map_sum,map_sum,map_sum,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑g,‖π (y g)-π (z g)‖:=norm_sum_le _ _
    _ ≤ ∑_:Grades d,(C.S.a m)^h*Real.exp (-σ*C.S.scale m):=Finset.sum_le_sum fun g _=>bound g
    _ = _ :=by simp

end YM.Integration.WilsonMacroscopicRichCaptureClass
