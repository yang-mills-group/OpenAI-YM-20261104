import YM.Integration.WilsonThermometerUnitFilingFourPoolArms

/-! The uncorrected weak columns at the requested physical radius have a
rooted price on the original ordered Wilson limit. The same station enrolls
every vector of every admitted grade. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFourWeakWall
open Function Filter Set Extraction Table Spec Lattice RG Wilson
open GapsContact GapsContact.Stamps GapsContact.Seams GapsContact.Ascent
open Trace Trace.Terrace Trace.Pilot Next.UVStress Climb MergeProof.East
open WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (simple : G.Simple) {l : Ultrafilter (ℕ×ℕ)}
variable {H : (Bel C.book).Hierarchy} {J : Scaling S} {V : ∀ k, Vane C k}
variable {Y : ∀ (d : ℕ) (_ : ℕ), (Bel C.book).Field d →L[ℂ] C.label d}

include F simple in
theorem quote (book : Gondola f H J l V Y) (d : ℕ) :
    ∃ B : ℝ, ∀ᶠ k in atTop, ∀ a : (Bel C.book).Field d,
    ∀ᶠ z : ℕ×ℕ in f.fuse, OPE.Cards.PaidAt C.S z.1 z.2 (purchaseWidth (V k))
      (C.beta z.1 z.2) (B*‖a‖) (C.O z.1 z.2 (heightV V k d z a) 0) := by
  let K : Module.Basis (PegC C d) ℂ ((Bel C.book).Field d) := PoleC C d
  choose bill pos earned using fun t : PegC C d =>
    WilsonThermometerUnitFilingFourWall.original book F.room.cutoff 1 (by norm_num) one_lt_two simple t
  let coord (t : PegC C d) := (K.coord t).toContinuousLinearMap
  refine ⟨∑ t, ‖coord t‖*bill t,?_⟩
  filter_upwards [eventually_all.mpr earned] with k eq a
  let m := purchaseWidth (V k)
  have floor : ∀ᶠ z : ℕ×ℕ in f.fuse, m ≤ z.1 := by
    rw [Extraction.Order.fused]
    unfold Extraction.Order.late
    exact Eventually.of_forall fun _ => f.mesh.cofinal.eventually_ge_atTop m
  filter_upwards [eventually_all.mpr eq, floor] with z keys live
  let W := Cells.center C.S z.2 live 0
  let b := C.beta z.1 z.2
  let op := ((C.linearO z.1 z.2 d 0).mk' _).comp (heightV V k d z).toLinearMap
  have receipts (t : PegC C d) :
      Cells.Interior (W.chamber 0) (op (K t)) ∧ W.rootTest b (op (K t)) ≤ bill t :=
    (keys t).choose_spec.2 0
  have lin : op a = ∑ t, K.repr a t • op (K t) := by
    conv_lhs => rw [← K.sum_repr a, map_sum]
    simp_rw [map_smul]
  obtain ⟨inside,fee⟩ := Next.Extract.rooted W b (Cells.seamless F.room.cutoff ..)
    Finset.univ (fun t => op (K t)) (fun t => K.repr a t) (fun t _ => (receipts t).1)
  change OPE.Cards.PaidAt _ _ _ _ _ _ (op a)
  rw [lin]
  refine ⟨live,inside,fee.trans ?_⟩
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro t _
  rw [mul_right_comm ‖coord t‖]
  exact mul_le_mul ((coord t).le_opNorm a) (receipts t).2 (Cells.Tiling.root_nonneg ..) (by positivity)

/-- The actual untouched Vane and the public label it represents. -/
structure Purchased (F : Final C f S) (H : (Bel C.book).Hierarchy)
    (l : Ultrafilter (ℕ×ℕ)) (r : ℝ) (c : ℕ) : Prop where
  station : ∃ (k : ℕ) (cap : c ≤ k) (W : Vane C k), W.checked f H k ∧ W.wheel.r = r ∧ c ≤ W.k ∧
    (0 < purchaseWidth W ∧ 20*C.S.a (purchaseWidth W) < C.S.a (purchaseWidth W-1) ∧
      C.S.a (purchaseWidth W-1) < r*LogV r/32) ∧
    ∀ d : Fin (c+1), ∃ T : Spin.change S d, ∀ a : (Bel C.book).Field d,
      ∃ y : Arm C S (l:Filter _) d (T a),
        (∀ z, y.source z = W.wheel.atCut z ⟨d,(Nat.lt_of_le_of_lt (Nat.le_of_lt_succ d.isLt) (Nat.lt_succ_of_le cap))⟩ a) ∧
        ∀ᶠ z : ℕ×ℕ in f.fuse, OPE.Cards.PaidAt C.S z.1 z.2 (purchaseWidth W)
          (C.beta z.1 z.2) (dock r*‖a‖) (C.O z.1 z.2 (y.source z) 0)

include simple in
theorem original {arch : Arch C} (bliss : Bliss F l arch H) (c : ℕ) :
    ∀ᶠ r in trail, Purchased F H l r c := by
  by_contra no
  obtain ⟨s,hs,excluded⟩ := contradictionTrail _ no
  obtain ⟨m,hm,X,hX,V,script⟩ := bliss.picks s (hs.mono_right nhdsWithin_le_nhds)
    (fun n => (excluded n).1)
  obtain ⟨Y,book⟩ := script.meters
  choose B fee using fun d : Fin (c+1) => quote F simple book d
  have growing : Tendsto (fun k => dock (X.r k)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (Over.a_clock (J:=X))
  have ranks := eventually_all.mpr fun d : Fin (c+1) =>
    ((fee d).and (book.terminal d)).and (growing.eventually_ge_atTop (B d))
  obtain ⟨k,cap,coarse,room,prices⟩ := ((eventually_ge_atTop c).and
    ((book.growth.eventually_ge_atTop c).and ((overhang book simple bliss.budgets).and ranks))).exists
  apply (excluded (m k)).2
  rw [← show X.r k = s (m k) from congr_fun hX k]
  refine ⟨k,cap,V k,(book.season k).1,(book.season k).2,coarse,room,fun d => ?_⟩
  have ok : d.val ≤ k := (Nat.le_of_lt_succ d.isLt).trans cap
  obtain ⟨⟨pay,lands,files⟩,funded⟩ := prices d
  refine ⟨X.U k d,fun a => ?_⟩
  have ev : Continuous (fun A : (Bel C.book).Field d →L[ℂ] C.label d => A a) :=
    continuous_id.clm_apply continuous_const
  let cut := fun z : ℕ×ℕ => heightV V k d z a
  let y : Arm C S (l:Filter _) d (X.U k d a) :=
    ⟨cut,Y d k a,ev.continuousAt.tendsto.comp lands,(files a).symm⟩
  refine ⟨y,fun z => ?_,?_⟩
  · simp only [y,cut,heightV,dif_pos ok]
  · filter_upwards [pay a] with z q
    exact ⟨q.live,q.ticket,q.mark.trans (mul_le_mul_of_nonneg_right funded (norm_nonneg _))⟩

end YM.Integration.WilsonThermometerUnitFilingFourWeakWall
