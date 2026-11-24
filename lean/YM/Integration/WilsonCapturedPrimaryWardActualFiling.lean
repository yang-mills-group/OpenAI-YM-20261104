import YM.Integration.WilsonCapturedPrimaryWardRestoration

/-! The same measured fixed-u counterterm against the actual Wilson fields.
The Haar equation remainder is consumed at fixed physical radius in the original
UV-then-volume extraction. No equation field is erased in a held conditional law. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardActualFiling
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Push
open Extraction Extra.Histories PhysicalNext.Repeat.Legato
open Bandage Stock RG16.Literal RG05Readout Native Address Many Records Harvest Copper
open RG12 RG17 Climb Trace.Pilot MergeProof Next.Extract PhysicalNext.Repeat Legato
open MergeProof.Ribbons MergeProof.Ribbons.ManyCopies Cells Accent Motion
open Trace.Physical.GermGraph GridApprox Next.Rank Ribbon Trace.Physical
open XSpace XSpace.Rose Push.GridApprox OPE OPE.Cards OPE.Orbits Spec
open WilsonCapturedPrimaryPhysicalArray WilsonCapturedPrimaryActiveArms
open WilsonCapturedPrimaryFaceWallet WilsonThermometerOwnOffsetField WilsonReflectedPhysicalRate
open WilsonCapturedPrimaryWardRestoration
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {n : ℕ} {f : Extraction.Order}
variable (V : ∀ d, SectionData (R.family.labels.level d)) (W : Mark.Weave G)
  (P : ∀ d, (ℕ×ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d)) (b : Presentation R.family)

theorem bounded (room : CellHyp R.family f) (simple : G.Simple)
    (slow : WilsonWindowReportingPace.Slow R.kit) (v J : ℕ) (wide : 4 < v)
    (φ : Test n) (d : Fin n → ℕ)
    (portfolio : ∀ d, Mark.Portfolio R.family.params (V d) (W d))
    (issued : Hearthside R.family V W P b (Bandage.fly R.alloy.B.a)) :
    ∀ᶠ r : ℝ in 𝓝[>]0, ∀ M : ℝ, 0 ≤ M → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ z : ℕ × ℕ in f.fuse, ∀ (o : Fin n → Site (R.family.side z.1 z.2)),
    WilsonCenteredCompactBooking.mass R φ r z o ≠ 0 → ∀ (axis : Option (Fin n)) (s : Finset (Fin n))
      (x : (i : Fin n)→R.family.label (d i)), (∀ i∈s, ‖x i‖ ≤ M) →
      PaidAt R.family.S z.1 z.2 J (R.family.beta z.1 z.2) ε
        (filed R d x s (registered o axis)-WilsonCapturedPrimaryWardFaces.adjusted R V P b d x s (registered o axis)) := by
  obtain ⟨A,nn,paid⟩ := WilsonCapturedPrimaryWardRestoration.original R V W P b room simple slow v J wide φ d portfolio issued
  filter_upwards [paid] with r bill
  obtain ⟨k,ready⟩ := bill.exists
  intro M hM ε pos
  let weight (i:Fin n) := A i*R.family.S.a k^(-(d i:ℝ)-1)+1+2*Fintype.card (R.family.labels.level (d i)).Index
  let mass (s:Finset (Fin n)) := (((2:ℕ)^s.card-1:ℕ):ℝ)*∏ i∈s,(weight i*(1+M))
  let δ (z:ℕ×ℕ) := Real.exp (-(1/64:ℝ)*R.family.S.scale z.1)
  have gone : Tendsto δ f.fuse (𝓝 0) := Real.tendsto_exp_atBot.comp
    (Tendsto.const_mul_atTop_of_neg (by norm_num) (R.family.S.divergent.comp (WilsonCapturedPrimaryWardRestoration.upper f)))
  have small (s:Finset (Fin n)) : ∀ᶠ z:ℕ×ℕ in f.fuse, δ z * mass s ≤ ε := by
    have limit : Tendsto (fun z=>δ z*mass s) f.fuse (𝓝 0) := by simpa using gone.mul_const (mass s)
    exact (limit.eventually (gt_mem_nhds pos)).mono fun _ hz=>le_of_lt hz
  filter_upwards [ready,eventually_all.mpr small] with z heard cheap
  obtain ⟨h,entry⟩ := heard
  intro o nz axis s x norm
  obtain ⟨ok,cap⟩ := entry o nz axis s x
  refine ⟨h,ok,cap.trans (le_trans ?_ (cheap s))⟩
  dsimp only [mass]
  have wp (i:Fin n) : 0 ≤ weight i := by dsimp [weight]; positivity [nn i,R.family.S.a_pos k]
  have tot : ∏ i∈s, factor R k (d i) (A i) (x i) ≤ ∏ i∈s,(weight i*(1+M)) := by
    apply Finset.prod_le_prod
    · intro i _
      exact mul_nonneg (wp i) (by positivity)
    · intro i hi
      exact mul_le_mul_of_nonneg_left (by linarith only [norm i hi]) (wp i)
  calc
    _ ≤ (((2:ℕ)^s.card-1:ℕ):ℝ)*δ z*∏ i∈s,(weight i*(1+M)) :=
      mul_le_mul_of_nonneg_left tot (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
    _ = _ := by ring

private lemma combine {N p J : ℕ} {F A H : Config G (R.family.side N p) → ℂ} {w e:ℝ}
    (h : PaidAt R.family.S N p J (R.family.beta N p) w (A-H))
    (r : PaidAt R.family.S N p J (R.family.beta N p) e (F-A)) :
    PaidAt R.family.S N p J (R.family.beta N p) (w+e) (F-H) := by
  have sum : F-H=(A-H)+(F-A) := by abel
  rw [sum]
  refine ⟨h.live,h.ticket.plus r.ticket,?_⟩
  exact ((seamless R.makes N p).semi _ _ _ h.ticket r.ticket).trans (add_le_add h.mark r.mark)

variable [NeZero n]
/-- Each fixed earlier report is literally that of the projected registered face.
The full measured Wilson product uses the same field and an arbitrary additional
UV tolerance on any fixed bounded family of submitted coordinates. -/
theorem original (room : CellHyp R.family f) (simple : G.Simple)
    (book : OPE.Package R.family R.w (mutt R.alloy.B.a R.Q) R.doors)
    (shop : RG05Preconstruction.ReadoutPurchase R.b) (slow : WilsonWindowReportingPace.Slow R.kit)
    (D v h J u : ℕ) (wide : 4 < v) (enlarged : R.family.ref h ≤ J)
    (station : ∀p, Opened R.family h u p) (tiling : Stock.Tabs.opens R.family.path.levels 1 J u)
    (φ : Test n) (d : Fin n → ℕ) (cap : ∀i,d i ≤ D)
    (portfolio : ∀ d, Mark.Portfolio R.family.params (V d) (W d))
    (issued : Hearthside R.family V W P b (Bandage.fly R.alloy.B.a)) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ r in trail, let m := capture R r
    let k := launch R simple v r
    ∃ (um : u ≤ m) (mk : m+1 < k), ∀ M : ℝ, 0 ≤ M → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ z : ℕ × ℕ in f.fuse, ∃ kn : k < z.1, ∀ o : Fin n → Site (R.family.side z.1 z.2),
      WilsonCenteredCompactBooking.mass R φ r z o ≠ 0 → ∀ ax : Fin n,
      ∃ S : Shelf (N:=z.1) (p:=z.2) R k d (registered o (some ax)),
      let un := um.trans (m.le_succ.trans (mk.le.trans kn.le))
      let w := K*r^((h:ℝ)+1/32)
      S.serves kn.le un J (station z.2) w ∧
      ∀ (s : Finset (Fin n)) (x : (i:Fin n) → R.family.label (d i))
        (y : (i:Fin n) → Palette R.family (level d s i)), (∀ i∈s, ‖x i‖ ≤ M) →
        WilsonCapturedPrimaryNamedReturn.primary R (p:=z.2) (level d s) (S.paths s) kn.le
          (label R s (fun i=>b.step (d i) z (x i))) y →
        let H := WilsonCapturedPrimaryWardFaces.projected R b d x s (registered o (some ax))
        let c := WilsonMacroscopicRichChildRegistration.returned R.family R.makes (station z.2) un H
        let price := ((∏ i∈s,(1+size (y i)))*2^(n-s.card))*w
        Booked R.family z.1 z.2 h H u un ∧ PaidAt R.family.S z.1 z.2 J (R.family.beta z.1 z.2)
          (price+ε) (filed R d x s (registered o (some ax))-R.family.O z.1 z.2 c 0) := by
  obtain ⟨K,one,paid⟩ := WilsonCapturedPrimaryWardReturn.original R V W P b simple book shop slow D v h J u
    wide enlarged station tiling φ d cap portfolio issued
  have UV := bounded R V W P b room simple slow v J wide φ d portfolio issued
  refine ⟨K,one,?_⟩
  filter_upwards [paid,UV] with r native adjust
  obtain ⟨um,mk,call⟩ := native
  refine ⟨um,mk,fun M nonneg ε pos=>?_⟩
  filter_upwards [adjust M nonneg ε pos,(WilsonCapturedPrimaryWardRestoration.upper f).eventually_gt_atTop (launch R simple v r)]
    with z restored kn
  refine ⟨kn,?_⟩
  intro o active ax
  obtain ⟨S,sale,matched⟩ := call z.1 z.2 kn o active ax
  refine ⟨S,sale,?_⟩
  intro s x y norm input
  obtain ⟨enrolled,_,charged⟩ := matched s x y input
  exact ⟨enrolled,combine R charged (restored o active (some ax) s x norm)⟩

end YM.Integration.WilsonCapturedPrimaryWardActualFiling
