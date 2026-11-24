import YM.Integration.WilsonPhysicalMasterRoom
import YM.Integration.WilsonPrimitiveReportingCut

/-! Every homogeneous branch of the measured moving field has a complete
finite Wilson coefficient on the genuine full reporting window. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFundedReportingBranch
open Function Set Filter Lattice Wilson RG MergeProof OPE OPE.Orbits OPE.Cards Spec PhysMS
open RG16 RG16.Literal Trace.Physical.GermGraph WilsonMasterReportingWords
open PhysicalNext.Repeat.Legato MergeProof.Accent
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] [Nonempty I] {d : I → ℕ}

omit [Nonempty I] in
theorem joint (F : Spec.Final C f S)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → tower S) (H : Leading F J) (hG : G.Simple)
    (e : I → ℕ) (leGrade : ∀ i, e i ≤ d i) (B : ℝ) :
    ∃ A : ℕ → ℝ, RateIs atTop C.S.scale A 0 ∧ ∀ᶠ m in atTop,
      ∀ r ∈ Icc (C.S.a m) (WilsonReportingLength.radius C B m), ∀ N p (hm : m < N)
      (op : ∀ i, Opened C (e i) m p) (v : (i : I) → (Climb.Bel C.book).Field (d i)),
      (∀ i, ‖v i‖ ≤ 1) → ∀ i, (C.labels.level (e i)).coeffSize
        (coordinates F.room.cutoff N p _ m (op i) hm.le
          (S.representative _ (R.cutTest _ _ (J r _ (v i))))) ≤ A m := by
  choose A rate all using fun i => WilsonPhysicalMasterRoom.purchased
    F R J H hG (e i) (d i) (leGrade i) B
  let room (m : ℕ) := 1 + ∑ i, ‖A i m‖
  have lb (m : ℕ) : 1 ≤ room m := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => norm_nonneg _)
  have total := RateLE.sum (S:=Finset.univ) C.S.divergent
    (fun i _ => (rate i |>.pays C.S.divergent).norm)
  have priced : RateIs atTop C.S.scale room 0 := RateIs.of_sandwich
    (RateIs.const (c:=1) C.S.divergent one_pos) ((RateLE.const (1:ℝ) C.S.divergent).add total C.S.divergent)
    (Eventually.of_forall lb) (Eventually.of_forall fun _ => le_rfl) C.S.divergent
  refine ⟨room,priced,?_⟩
  filter_upwards [eventually_all.mpr all] with m hm
  intro r hr N p cut op v hv i
  apply (hm i r hr N p cut (op i) (v i) (hv i)).trans
  apply (Real.le_norm_self (A i m)).trans
  exact (Finset.single_le_sum (f:=fun i => ‖A i m‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)).trans
    (le_add_of_nonneg_left zero_le_one)

theorem purchased (F : Spec.Final C f S)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → tower S) (H : Leading F J) (fac : Facilities C f S)
    (pace : ∀ m, ((C.S.block m).val : ℝ) ≤ Real.log (Lambda C.path.levels m))
    (e : I → ℕ) (leGrade : ∀ i, e i ≤ d i) (h top stop : ℕ)
    (starts : Stock.Tabs.opens C.path.levels 1 top stop) (openStop : ∀ p, Opened C h stop p)
    (η M B : ℝ) (hη : 0 < η) (hM : 0 < M) (hB : 20 < B) :
    ∃ E rem : ℕ → ℝ, RateIs atTop C.S.scale E (-h) ∧ RateIs atTop C.S.scale rem (-h) ∧
      ∀ᶠ m : ℕ in atTop, let b := port C (8*M) B (mul_pos (by norm_num) hM) m
        ∃ (hs : stop ≤ b) (hb : b+1 < m), ∀ p,
          ∃ _op : ∀ i, Opened C (e i) m p, ∀ N (hm : m < N) (ρ : ℝ) (x : I → Cover)
           (v : (i : I) → (Climb.Bel C.book).Field (d i)),
          Tuple C M η B m ρ x → (∀ i, ‖v i‖ ≤ 1) →
          let r := C.S.a m * ρ
          let Y := ∏ i, C.O N p (S.representative _ (R.cutTest (e i) (d i)
            (J r _ (v i)))) (Cells.location C.S m N p (x i))
          ∃ z Q, Funds C F.room.cutoff p N b h top stop (E m) (rem m) (weight C h m)
            Y starts.1 hs ((Nat.le_succ b).trans (hb.le.trans hm.le)) (openStop p) z Q ∧
            PaidAt C.S N p top (C.beta N p) (2*(stakes C top stop / weight C h m))
              (Y-C.O N p z 0) := by
  obtain ⟨A,Aprice,allowance⟩ := joint F R J H fac.simpleGate e leGrade (B+1)
  obtain ⟨_,_,_,L⟩ := fac.costlier
  obtain ⟨E,rem,rate,remRate,purchase⟩ := expenses C fac.simpleGate L.toPackage F.room.cutoff
    e h top stop A Aprice η M B hη hM hB pace starts openStop
  refine ⟨E,rem,rate,remRate,?_⟩
  filter_upwards [allowance,purchase] with m credit sizes
  obtain ⟨hs,hb,steps⟩ := sizes
  refine ⟨hs,hb,fun p => ?_⟩
  obtain ⟨op,menu⟩ := steps p
  refine ⟨op,fun N hm ρ x v layout unit => ?_⟩
  let r := C.S.a m*ρ
  have valid : r ∈ Icc (C.S.a m) (WilsonReportingLength.radius C (B+1) m) := by
    have one := Real.one_le_rpow (one_le_two.trans (lambda_up C m).le) (show 0 ≤ B by linarith)
    exact ⟨le_mul_of_one_le_right (C.S.a_pos m).le (one.trans layout.lo),
      mul_le_mul_of_nonneg_left layout.hi (C.S.a_pos m).le⟩
  let raw (i : I) := S.representative (e i) (R.cutTest (e i) (d i) (J r _ (v i)))
  let incoming i := coordinates F.room.cutoff N p (e i) m (op i) hm.le (raw i)
  obtain ⟨z,Q,price⟩ := menu N hm ρ x incoming layout (credit r valid N p hm op v unit)
  have cell := replica F.room.cutoff N p m hm.le op x raw
  change Words C F.room.cutoff e p N m incoming x hm.le op = _ at cell
  rw [cell] at price
  exact ⟨z,Q,price,starts.1.trans (hs.trans ((Nat.le_succ _).trans (hb.le.trans hm.le))),
    price.inview,price.packing⟩

end YM.Integration.WilsonFundedReportingBranch
