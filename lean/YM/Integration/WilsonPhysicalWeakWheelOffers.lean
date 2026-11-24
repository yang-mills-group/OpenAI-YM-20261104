import YM.Integration.WilsonAddressedPublicCardWall
import YM.Integration.WilsonPositionThermometerCapStation

/-! A physical weak wall with the very same scaling arrows as the enrolled Bliss script. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalWeakWheelOffers
open Function Filter Set Extraction Table Spec Lattice RG Wilson
open GapsContact GapsContact.Stamps GapsContact.Seams GapsContact.Ascent
open Trace Trace.Terrace Trace.Pilot Next.UVStress Climb MergeProof.East
open WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (F:Final C f S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel C.book).Hierarchy}{arch:Arch C}
variable {X:Scaling S}{V:∀k,Vane C k}

structure Offered {c k:ℕ} (cap:c≤k)(W:Vane C k)(r:ℝ)(T:∀d:Fin (c+1),Spin.change S d):Prop where
  live:c≤W.k
  width:0<purchaseWidth W ∧ 20*C.S.a (purchaseWidth W)<C.S.a (purchaseWidth W-1) ∧
    C.S.a (purchaseWidth W-1)<r*LogV r/32
  physical:C.S.a (purchaseWidth W)≤r*(C.path.levels.clock.monitor W.k)^5
  blocks:∀i:ℕ,i≤W.k→((C.S.block i).val:ℝ)≤C.path.levels.clock.monitor W.k
  rows:∀d:Fin (c+1),(∀v:S.Field d,‖(T d).symm v‖≤dock r*cost F d r v) ∧
    ∀a:(Bel C.book).Field d,∃y:Arm C S (l:Filter _) d (T d a),
      (∀z,y.source z=W.wheel.atCut z ⟨d,Nat.lt_succ_of_le ((Nat.le_of_lt_succ d.isLt).trans cap)⟩ a) ∧
      ∀ᶠz:ℕ×ℕ in f.fuse,OPE.Cards.PaidAt C.S z.1 z.2 (purchaseWidth W) (C.beta z.1 z.2)
        (dock r*‖a‖) (C.O z.1 z.2 (y.source z) 0)

theorem lift {k:ℕ}(W:Vane C k)(valid:W.checked f H k)(below:(l:Filter _)≤f.fuse):
    ∃ L:Lifts C k,Tendsto W.wheel.atCut (l:Filter _) (𝓝 L):=by
  obtain ⟨A,hA⟩:=valid.fares.lift_bound
  obtain ⟨b,hb,_,Y,hY⟩:=finite_extract (𝓛:=(l:Filter _)) W.wheel.atCut A
    ((show ∀ᶠi:ℕ×ℕ in f.fuse,‖W.wheel.atCut i‖≤A from hA).filter_mono below)
  exact ⟨Y,(l.unique hb) ▸ hY⟩

theorem along (simple:G.Simple)(bliss:Bliss F l arch H)
    (script:Over.Scribe f X V arch F.sector l F.room.kernel H)(c:ℕ):
    ∀ᶠ k in atTop,∃cap:c≤k,Offered F (l:=l) cap (V k) (X.r k) (fun d=>X.U k d):=by
  obtain ⟨Y,book⟩:=script.meters
  choose B fee using fun d : Fin (c+1) => WilsonThermometerUnitFilingFourWeakWall.quote F simple book d
  choose A _ fit using fun d : Fin (c+1) => window_prices F simple script.monorail d.val 1 1 one_pos
  have growing : Tendsto (fun k => dock (X.r k)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (Over.a_clock (J:=X))
  have ranks := eventually_all.mpr fun d : Fin (c+1) =>
    (((fee d).and (book.terminal d)).and (growing.eventually_ge_atTop (B d))).and
      ((fit d).and (growing.eventually_ge_atTop (A d)))
  have widths:=book.growth.eventually ((inch_upper C.path.levels simple bliss.budgets).and
    (block_upper C.path.levels simple bliss.budgets))
  filter_upwards [eventually_ge_atTop c,book.growth.eventually_ge_atTop c,
    overhang book simple bliss.budgets,widths,ranks] with k cap coarse room width prices
  obtain ⟨sharp,blocks⟩:=width
  have positive:0<(V k).b:=lt_trans (by norm_num : (0:ℝ)<5) (book.season k).1.high.1
  have fee:= (div_le_iff₀ (C.S.a_pos (V k).k)).mp (sharp (V k).b positive)
  have purchase:C.S.a (purchaseWidth (V k)) ≤ X.r k*(C.path.levels.clock.monitor (V k).k)^5:=by
    rw [←(book.season k).2]
    change _ ≤ (C.S.a (V k).k*Next.Rank.Station.mag C.path.levels (V k).b (V k).k)*_
    calc
      _ ≤ _ := fee
      _ = _ := by ring
  refine ⟨cap,coarse,room,purchase,blocks,fun d=>?_⟩
  have ok : d.val ≤ k := (Nat.le_of_lt_succ d.isLt).trans cap
  obtain ⟨⟨⟨pay,lands,files⟩,funded⟩,win,lower⟩ := prices d
  refine ⟨?_,fun a => ?_⟩
  · intro a
    have available:‖(X.U k d).symm a‖ ≤ A d*cost F d (X.r k) a:=by
      simpa only [LinearEquiv.apply_symm_apply] using (win ((X.U k d).symm a)).1
    exact available.trans (mul_le_mul_of_nonneg_right lower (cost_pos F ..))

  have ev : Continuous (fun A : (Bel C.book).Field d →L[ℂ] C.label d => A a) :=
    continuous_id.clm_apply continuous_const
  let cut := fun z : ℕ×ℕ => heightV V k d z a
  let y : Arm C S (l:Filter _) d (X.U k d a) :=
    ⟨cut,Y d k a,ev.continuousAt.tendsto.comp lands,(files a).symm⟩
  refine ⟨y,fun z => ?_,?_⟩
  · simp only [y,cut,heightV,dif_pos ok]
  · filter_upwards [pay a] with z q
    exact ⟨q.live,q.ticket,q.mark.trans (mul_le_mul_of_nonneg_right funded (norm_nonneg _))⟩

end YM.Integration.WilsonPhysicalWeakWheelOffers
