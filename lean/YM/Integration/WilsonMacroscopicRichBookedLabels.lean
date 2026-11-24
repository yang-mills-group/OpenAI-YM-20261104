import YM.Integration.WilsonMacroscopicRichFilingNorm
import YM.Integration.WilsonMeasuredReportingProduct

/-! The fixed reporting tuple buys one true raw earlier-field bound for all finer cutoffs and periods. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichBookedLabels
open Filter Function Set Spec OPE OPE.Orbits PhysMS Cells Wilson Lattice
open RG16 RG16.Literal Trace.Physical.GermGraph FilteredWilsonProduct FilteredIntrinsicGramReadout
open RG MergeProof Bid
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable {I:Type}[Fintype I][Nonempty I]{d:I→ℕ}

theorem purchased (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower S)(leading:Leading F J)(fac:Facilities C f S)
    (pace:∀m,((C.S.block m).val:ℝ)≤Real.log (Lambda C.path.levels m))
    (h top u:ℕ)(T:Stop C h top u)(η M B:ℝ)(hη:0<η)(hM:0<M)(hB:20<B):
    ∀ᶠ m : ℕ in atTop, ∃ (hu : u ≤ m), ∃ K : ℝ, ∀ N p (hm : m < N) (ρ : ℝ) (x : I → Cover)
      (v:(i:I)→(Climb.Bel C.book).Field (d i)),Tuple C M η B m ρ x→
      (∀i,‖v i‖≤1)→ ‖label (w:=(N,p)) F.room.cutoff (T.doors p) (hu.trans hm.le)
        (field F R J v (C.S.a m*ρ) m x (N,p))‖≤K:=by
  obtain ⟨E,rem,_,book⟩:=WilsonReportingProductInvoice.purchased (d:=d) F R J leading fac pace
    h top u T.live T.doors η M B hη hM hB
  filter_upwards [book] with m atDate
  let b:=port C (8*M) B (mul_pos (by norm_num) hM) m
  obtain ⟨ub,bm,bank⟩:=atDate
  have um : u ≤ m := ub.trans ((Nat.le_succ b).trans bm.le)
  obtain ⟨A,B',_,_,earned⟩:=WilsonMacroscopicRichFilingNorm.limits F.room.cutoff T.doors ub
  let costs (g:Grades d):=A*(2*E g m)+B'*(2*(E g m/gainChart C.path b u))
  refine ⟨um,∑g,costs g,?_⟩
  intro N p hm ρ x v tuple cap
  have bN : b ≤ N := (Nat.le_succ b).trans (bm.le.trans hm.le)
  let Y (g:Grades d):= WilsonReportingProductInvoice.source F R J v (C.S.a m*ρ) m N p x g
  obtain ⟨z,portfolios,_⟩:=bank N p hm ρ x v tuple cap
  choose Q guild using portfolios
  have priced (g:Grades d):‖label (w:=(N,p)) F.room.cutoff (T.doors p) (ub.trans bN) (Y g)‖≤costs g:=
    earned N p bN (Y g) (z g) (E g m) (guild g).capZ (guild g).currency
  have booked (g:Grades d):Booked C N p h (Y g) u (ub.trans bN):=(guild g).works u le_rfl ub
  have cont (g:Grades d):Continuous (Y g):=by
    change Continuous (∏ i, C.O N p (component F R J v g (C.S.a m*ρ) i)
      (location C.S m N p (x i)))
    rw [show (∏ i,C.O N p (component F R J v g (C.S.a m*ρ) i)
      (location C.S m N p (x i)))=fun U=>∏ i,C.O N p
      (component F R J v g (C.S.a m*ρ) i) (location C.S m N p (x i)) U
      from funext fun _=>Finset.prod_apply ..]
    exact continuous_finsetProd _ fun _ _=>C.continuousO ..
  have collect:= (IntrinsicProductLinearity.booked_sum C N p h u F.room.cutoff (T.doors p)
    (ub.trans bN) (fun _:Grades d=>(1:ℂ)) Y cont booked).2
  simp only [one_smul] at collect
  have exactField:field F R J v (C.S.a m*ρ) m x (N,p)=∑g,Y g:=by
    rw [field_expansion]
    rfl
  unfold label
  rw [exactField,collect,map_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _=>priced g)

end YM.Integration.WilsonMacroscopicRichBookedLabels
