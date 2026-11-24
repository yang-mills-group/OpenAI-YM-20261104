import YM.Integration.WilsonReportingPrescribedOldGas
import YM.Integration.WilsonSeparatedOriginalLedgerGas

/-! On a fixed nonbare Wilson field, every connected coefficient with at
least two names in the old reference minus the fresh complete Q program is
exactly the corresponding connected coefficient of the complete old gas. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingPrescribedOldConnected
open Function Finset Set Lattice Wilson RG Source Labels Marker Multi FVA1 Extra.Histories
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address Extra.Trajectories
open RG05Readout RG05Readout.Many RG05Readout.Address MergeProof Accent Menu MergeProof.Replicums
open RG3.Held RG3.Script.Picnic Extraction Table Spec RG12 RG17 MS MS.Menus MS.Local.Physical
open WilsonAllDateHarvestPropagation WilsonReportingPrescribedOldGas WilsonSeparatedOriginalLedgerGas
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V : Type} [Fintype V] [DecidableEq V] (J : Census V)

private theorem off (f : V → ℂ) (s : J.Mode) (large : 2 ≤ s.val.card) : (Mach J f).part s = 0 := by
  unfold Mach
  rw [Poly.part_sum]
  apply Finset.sum_eq_zero
  intro v _
  rw [Poly.part_send,if_neg]
  intro eq
  have card := congrArg (fun j : J.Mode => j.val.card) eq
  simp only [Census.fire,Finset.card_singleton] at card
  omega

theorem mixed (P : Rep G n) (rows : V → Three G n) (X : V → Config G n → ℂ)
    {a b : ℝ} (legal : P.activities.Valid P.p a b) (W : Config G n) (positive : 0 < P.eval W)
    (s : J.Mode) (large : 2 ≤ s.val.card) :
    (connected ((P.eval W : ℂ)⁻¹ • density (J:=J) P rows 0 0 W) -
       connected ((P.eval W : ℂ)⁻¹ • birth J P X W)).part s =
      (connected (old (J:=J) P rows 0 W)).part s := by
  let regular := Mach J (fun v => (rows v).2.1 W)
  let prescribed := Mach J (fun v => X v W)
  have nonzero : (P.eval W : ℂ) ≠ 0 := by exact_mod_cast positive.ne'
  have filled : (forced J P rows W).part J.quiet = (P.activities.gas P.p W : ℂ) := by
    apply stage₀ _ _ _ (mass_crest _ legal W)
    intro p
    simp [bar,Poly.bead,Poly.part_plus,Poly.part_send,mute]
  have shape : old (J:=J) P rows 0 W =
      (((P.eval W : ℂ)⁻¹)*(Real.exp (P.exponent W) : ℂ)) • forced J P rows W := by
    have same (p : Box n) : WilsonSeparatedOriginalLedgerGas.marked (J:=J) P rows 0 W p =
        bar P.activities J W p + Mach J (fun v => profile P.activities (rows v).2.2 p W) := by
      simp only [WilsonSeparatedOriginalLedgerGas.marked,Pi.zero_apply,add_zero]
    unfold old forced
    rw [funext same]
  have quiet : (old (J:=J) P rows 0 W).part J.quiet = 1 := by
    rw [shape,Poly.part_smul,filled]
    rw [mul_assoc,← Complex.ofReal_mul]
    exact inv_mul_cancel₀ nonzero
  have left : (P.eval W : ℂ)⁻¹ • density (J:=J) P rows 0 0 W =
      Poly.pass regular * old (J:=J) P rows 0 W := by
    unfold density restore
    simp only [Pi.zero_apply,Finset.sum_const_zero,add_zero,shape,smul_smul,Algebra.mul_smul_comm]
    rfl
  have right : (P.eval W : ℂ)⁻¹ • birth J P X W = Poly.pass prescribed := by
    rw [birth,smul_smul,inv_mul_cancel₀ nonzero,one_smul]
  rw [left,right,FormalOPE.RG10.PolyUtil.conn_mul (Poly.pass_part regular (mute J _)) quiet,
    FormalOPE.RG10.PolyUtil.conn_pass regular (mute J _),
    FormalOPE.RG10.PolyUtil.conn_pass prescribed (mute J _)]
  change (regular + connected (old (J:=J) P rows 0 W)).part s - prescribed.part s = _
  rw [Poly.part_plus,off J _ s large,off J _ s large,zero_add,sub_zero]

variable (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (L : Layout F) {B : Deck G} (Q : MS.Land.Prescription B) [Nonempty V]
local notation "Y" => R.family.path.rep

theorem original (hG : G.Simple) (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)
    (r : ℝ) (hr : 0 < r) {N per n : ℕ} (live : L.level r < N) {hn : n ≤ L.level r}
    (D : ActualRunQlocalNativeTuple.Datum R per (L.level r) n hn V)
    (age : ∀ s : ActualOriginalQReaders.Slot u, R.family.ref s.2.size ≤ L.level r)
    (z : V → Site (R.family.side N per))
    (placed : ∀ i, (R.family.S.toDepth live.le per).parent (z i) = ActualRunQlocalNativeTuple.root D i)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (rows : V → Three G (R.family.side (L.level r) per)) (W : Config G (R.family.side (L.level r) per))
    (s : J.Mode) (large : 2 ≤ s.val.card) :
    (connected (((Y N per (L.level r)).eval W : ℂ)⁻¹ • density (J:=J) (Y N per (L.level r)) rows 0 0 W) -
      connected (((Y N per (L.level r)).eval W : ℂ)⁻¹ • narrow (WilsonReportingPrescribedOldGas.admitted J)
        (((ActualOriginalQInput.input Q D u μ orders hG N live.le).leaf x).density W))).part s =
      (connected (old (J:=J) (Y N per (L.level r)) rows 0 W)).part s := by
  rw [WilsonReportingPrescribedOldReturn.original R F L r live Q hG u μ orders hr D age z placed x W,
    birth_choice]
  exact mixed J _ rows _ (R.makes.wilson.represents N per _ live.le).good.labels W
    (Multi.AxisShift.chosen_positive R.makes.wilson live.le W) s large

end YM.Integration.WilsonReportingPrescribedOldConnected
