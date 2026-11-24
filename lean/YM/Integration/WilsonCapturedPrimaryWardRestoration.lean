import YM.Integration.WilsonCapturedPrimaryWardMixed
import YM.Integration.WilsonCapturedPrimaryWardReturn

/-! The UV charge for restoring the named Wilson fields in the fixed
filing cell, on all masks of each occupied tuple of the true compact test. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardRestoration
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Push
open Extraction Extra.Histories PhysicalNext.Repeat.Legato
open RG12 RG17 Climb Trace.Pilot MergeProof Next.Extract PhysicalNext.Repeat Legato Bandage
open MergeProof.Ribbons MergeProof.Ribbons.ManyCopies Cells
open XSpace XSpace.Rose Push.GridApprox OPE OPE.Orbits RelayDifference
open WilsonCapturedPrimaryPhysicalArray WilsonOffsetReportingProducts WilsonOffsetEquationLaw
open WilsonAddressedEquationShelf
open private inside_sub from YM.Integration.WilsonCapturedPrimaryWardFile
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {n N p : ℕ}
variable (V : ∀ d, SectionData (R.family.labels.level d))
  (W : Mark.Weave G) (P : ∀ d, (ℕ×ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d))
  (b : Presentation R.family)

def filed (d : Fin n → ℕ) (x : (i : Fin n) → R.family.label (d i)) (s : Finset (Fin n))
    (o : Fin n → Site (R.family.side N p)) (U : Config G (R.family.side N p)) : ℂ :=
  ∏ i∈s,R.family.O N p (x i) (o i) U

def factor (k d : ℕ) (A : ℝ) (x : R.family.label d) : ℝ :=
  (A*R.family.S.a k^(-(d:ℝ)-1)+1+2*Fintype.card (R.family.labels.level d).Index)*(1+‖x‖)

theorem upper (f : Extraction.Order) : Tendsto Prod.fst f.fuse atTop :=
  tendsto_atTop.mpr fun j => (f.fused _).2 (Eventually.of_forall fun _=>f.mesh.cofinal.eventually_ge_atTop j)

private lemma move {d : ℕ} (x : R.family.label d) (o : Site (R.family.side N p)) :
    oriented (residual R.family (V d) N p (P d (N,p)) (x-b.step d (N,p) x) 0) false 1 o =
      residual R.family (V d) N p (P d (N,p)) (x-b.step d (N,p) x) o := by
  funext U
  simp only [RelayDifference.oriented,RelayDifference.hand,Bool.false_eq_true,if_false,pull_one,WilsonOffsetReportingProducts.residual,incoming,Family.O,
    TransferData.cylinder,Source.initial,Pi.smul_apply,Pi.sub_apply,SectionData.places_trans,zero_add]

/-- All coordinates may depend on both regulators. The finite factor retains that
dependence, so a later UV limit may use the actual measured reference wallet. -/
theorem original {f : Extraction.Order} (room : CellHyp R.family f)
    (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (v J : ℕ) (wide : 4 < v) (φ : Test n) (d : Fin n → ℕ)
    (portfolio : ∀ d, Mark.Portfolio R.family.params (V d) (W d))
    (issued : Hearthside R.family V W P b (Bandage.fly R.alloy.B.a)) :
    ∃ A : Fin n → ℝ, (∀ i, 0 ≤ A i) ∧ ∀ᶠ r : ℝ in 𝓝[>]0, ∀ᶠ k : ℕ in atTop,
    ∀ᶠ z : ℕ × ℕ in f.fuse, ∃ h : J ≤ z.1,
    ∀ (o : Fin n → Site (R.family.side z.1 z.2)), WilsonCenteredCompactBooking.mass R φ r z o ≠ 0 →
    ∀ (axis : Option (Fin n)) (s : Finset (Fin n)) (x : (i : Fin n) → R.family.label (d i)),
    let T := center R.family.S z.2 h 0
    let F := filed R d x s (registered o axis)
    let Y := WilsonCapturedPrimaryWardFaces.adjusted R V P b d x s (registered o axis)
    Interior (T.chamber 0) (F-Y) ∧ T.rootTest (R.family.beta z.1 z.2) (F-Y) ≤
      (((2:ℕ)^s.card-1:ℕ):ℝ)*Real.exp (-(1/64:ℝ)*R.family.S.scale z.1)*
        ∏ i ∈ s,factor R k (d i) (A i) (x i) := by
  choose k₀ A nn rent using fun i : Fin n=>WilsonCapturedPrimaryWardHome.measured R room (d i)
  refine ⟨A,nn,?_⟩
  have native := eventually_all.mpr (fun i : Fin n=>WilsonCapturedPrimaryWardHome.original R simple portfolio issued (d i))
  have houses := eventually_all.mpr (fun i : Fin n=>WilsonCapturedPrimaryWardRoom.original R.family J 0 (d i) (V (d i)))
  have sensors := eventually_all.mpr (fun i : Fin n=>near_center R.family J (d i) R.makes)
  filter_upwards [WilsonCapturedPrimaryWardNest.original R simple slow v J wide φ,
    WilsonCapturedPrimaryPhysicalChamber.original R J φ] with r ready chamber
  obtain ⟨early,bar⟩ := ready
  filter_upwards [bar,native,eventually_all.mpr (fun i : Fin n=>eventually_ge_atTop (k₀ i))] with k floor residuals old
  obtain ⟨fine,bill⟩ := floor
  filter_upwards [(upper f).eventually_ge_atTop k,
    (upper f).eventually_ge_atTop (WilsonCapturedPrimarySupportedHalo.date R r),
    (upper f).eventually (eventually_all.mpr residuals),eventually_all.mpr (fun i=>rent i k (old i)),
    (upper f).eventually houses,(upper f).eventually sensors,
    (upper f).eventually (R.family.S.divergent.eventually_ge_atTop 0)] with z live enough lower real localV source clock
  let h := early.trans (fine.trans live)
  refine ⟨h,?_⟩
  intro o active axis s x
  let loc := registered o axis
  let T := center R.family.S z.2 h 0
  let δ := Real.exp (-(1/64:ℝ)*R.family.S.scale z.1)
  have pos : 0 ≤ δ := (Real.exp_pos _).le
  have small : δ ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) clock)
  let g (i : s) (w : Site (R.family.side z.1 z.2)) :=
    residual R.family (V (d i)) z.1 z.2 (P (d i) z)
      (x i-b.step (d i) z (x i)) w
  let F (i : s) (w : Site (R.family.side z.1 z.2)) := R.family.O z.1 z.2 (x i) w
  let homeF (i:s) := F i 0
  let homeD (i:s) := g i 0
  let placedF (i:s) := F i (loc i)
  let placedD (i:s) := g i (loc i)
  let fee (i:s) := factor R k (d i) (A i) (x i)
  have fp (i:s) := real i (x i)
  have dp (i:s) := lower i z.2 (x i)
  have az (i:s) : 0 ≤ A i*R.family.S.a k^(-(d i:ℝ)-1) := by positivity [(nn i),(R.family.S.a_pos k)]
  have fpos (i:s) : 0 ≤ fee i := by dsimp [fee,factor]; positivity [az i]
  have fcost (i:s) : BlockCost (Q:=R.family.S) (homeF i) k (R.family.beta z.1 z.2) (fee i) := by
    refine ⟨(fp i).stop,(fp i).safe,(fp i).amount.trans ?_⟩
    dsimp [fee,factor]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
  have dcost (i:s) : BlockCost (Q:=R.family.S) (homeD i) k (R.family.beta z.1 z.2) (δ*fee i) := by
    refine ⟨(dp i).stop,(dp i).safe,(dp i).amount.trans ?_⟩
    change 2*(Fintype.card (R.family.labels.level (d i)).Index:ℝ)*‖x i‖*δ ≤ δ*fee i
    rw [mul_comm _ δ]
    apply mul_le_mul_of_nonneg_left _ pos
    dsimp [fee,factor]
    exact mul_le_mul (by linarith only [az i]) (by linarith : ‖x i‖ ≤ 1+‖x i‖)
      (norm_nonneg _) (by positivity [az i])
  have near := chamber z.1 z.2 enough o active axis
  have sf (i:s) : Interior (T.chamber 0) (placedF i) := source i h z.2 (loc i) (near i) (x i)
  have sd (i:s) : Interior (T.chamber 0) (placedD i) := by
    let y := x i-b.step (d i) z (x i)
    have e := incoming_continuous (V (d i)) z.1 z.2 (P (d i) z) y (loc i)
    apply inside_sub (source i h z.2 _ (near i) y)
    refine ⟨?_,e.measurable,?_,(Mark.cont_envelope e).cost⟩
    · intro l U
      simp only [incoming,Source.initial,Pi.smul_apply]
      rw [(V (d i)).placed_invariant (portfolio (d i)).valid _ _ l U]
    · exact fun U Z a=> incoming_local _ _ _ _ _ _ U Z
        (agrees_mono a (localV i h z.2 _ (near i)).2)
  have ink (t:Finset s) (_ : t ≠ ∅) :
      T.rootTest (R.family.beta z.1 z.2) (∏ i,t.piecewise placedD placedF i) ≤
        ∏ i,t.piecewise (fun j=>δ*fee j) fee i := by
    have q := bill z.1 z.2 live o active axis s (t.piecewise homeD homeF) (t.piecewise (fun j=>δ*fee j) fee)
      (fun i=>by by_cases hi:i∈t
                 · simpa [Finset.piecewise,hi] using dcost i
                 · simpa [Finset.piecewise,hi] using fcost i)
    suffices same : Contacts.Nested.clusterAt (fun i:s=>loc i) (t.piecewise homeD homeF)
        = ∏ i,t.piecewise placedD placedF i by rwa [same] at q
    funext U
    rw [Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i∈t
    · simpa only [Finset.piecewise,if_pos hi] using congrFun (move R V P b (x i) (loc i)) U
    · simp only [Finset.piecewise,if_neg hi,homeF,F,placedF,RelayDifference.oriented,RelayDifference.hand,Bool.false_eq_true,if_false,pull_one,
        R.family.translation,zero_add]
  have all := WilsonCapturedPrimaryWardMixed.original T (R.family.beta z.1 z.2)
    (seamless R.makes z.1 z.2) placedF placedD fee fpos sf sd pos small ink
  have agree : (∏ i,placedF i)-(∏ i,(placedF i-placedD i)) =
      filed R d x s loc - WilsonCapturedPrimaryWardFaces.adjusted R V P b d x s loc := by
    funext U
    simp only [filed,WilsonCapturedPrimaryWardFaces.adjusted,Pi.sub_apply,Finset.prod_apply,placedF,placedD,F,g]
    exact congrArg₂ (·-·)
      (Finset.prod_coe_sort (s:=s) (f:=fun i : Fin n=>R.family.O z.1 z.2 (x i) (loc i) U))
      (Finset.prod_coe_sort (s:=s) (f:=fun i : Fin n=>R.family.O z.1 z.2 (x i) (loc i) U -
        residual R.family (V (d i)) z.1 z.2 (P (d i) z) (x i-b.step (d i) z (x i)) (loc i) U))
  have prices : ∏ i,fee i = ∏ i∈s,factor R k (d i) (A i) (x i) :=
    Finset.prod_coe_sort (s:=s) (f:=fun i : Fin n=>factor R k (d i) (A i) (x i))
  rw [agree,prices] at all
  simpa only [δ,Fintype.card_coe] using all

end YM.Integration.WilsonCapturedPrimaryWardRestoration
