import YM.Integration.WilsonMatrixTicketLanesReflectedRank
import YM.Integration.WilsonMatrixTicketLanesReportedPrepaid

/-! Jointly buy the full spatial coefficient and the three complete, correlated, positive-coupling receipts. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesConnectedBudget
open Function Filter Set Real Lattice RG Wilson Tree Precision RG.Supply
open PhysicalNext PhysicalNext.Repeat ThroughLaunch Next.Foundations Push.PriceCompiler Input
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Parcel RGComparison.Core16.Silk
open RGComparison.Core16.Forge RGComparison.Core16.Lumen
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection WilsonMatrixTicketLanesReportedWords
open scoped Topology Classical BigOperators
variable {G : Gauge}

/-- Two independently submitted true microscopic letters, the desired order, and the real pin cap. -/
abbrev Request (G : Gauge) := (Letter G × Letter G) × ℕ × ℕ

def first (b : Request G) : Unit→Lamp G:=fun _=>lamp b.1.1
def second (b : Request G) : Unit→Lamp G:=fun _=>lamp b.1.2
def together (b : Request G) := WilsonMatrixTicketLanesReflectedGauge.pair (first b) (second b)
def absolute (b : Request G) := power (together b)+b.2.1

/-- The bound covers numerical values at every admissible coupling and every coefficient to the
same order on the same selected chamber, uniformly over all finite geometry and future pins. -/
def Income {I : Type} [Fintype I] {H : Patch} (K : KernelChoices) {P : Oven H} (X : P.Form G)
    (J : I→Lamp G) (q : ℕ) (x : ℝ) : Prop := ∃ U : Lumen.Stage,
    (sqrt (x/2))⁻¹ ≤ dollar U.L ∧ ∀ (c f : Side) (size : f.val=c.val*H.L.val),
    let S : StepData c f:=⟨H,K,size⟩
    Bid.Larger (G:=G) S → ∀ (T : Forest S.ratio) (u : Directions G c) (o : I→Site f),
      (∀i,‖u i‖≤X.Q) → Spool.Price U q (2+log x) (Spool.rank J S T X (Next.Foundations.chart G) u o) (Spool.reads J S u o)

private theorem income {I : Type} [Fintype I] {H : Patch} {K : KernelChoices} {P : Oven H} {X : P.Form G}
    (offer : P.Offers X K) (J : I→Lamp G) (q : ℕ) : ∀ᶠ x : ℝ in atTop,Income K X J q x:=by
  obtain ⟨U,C,_,_,sold⟩:=Spool.every J offer WilsonMatrixTicketLanesReportedPrepaid.start q (Next.Foundations.chart_ok G)
  have heat : Tendsto (fun x : ℝ=>(sqrt (x/2))⁻¹) atTop (𝓝 0):=
    tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop.comp (tendsto_id.atTop_div_const zero_lt_two))
  filter_upwards [heat.eventually (gt_mem_nhds (dollar_pos U.L)),
    (tendsto_atTop_add_const_left _ (2:ℝ) tendsto_log_atTop).eventually_ge_atTop C] with x cold enough
  refine ⟨U,le_of_lt (show _<dollar U.L from cold),?_⟩
  intro c f size S big T u o seated
  have price:=sold c f size big T u o seated
  exact ⟨fun i hi=>(price.growth i hi).trans enough,fun g gp window=>(price.cost g gp window).trans
    (mul_le_mul_of_nonneg_left enough (pow_nonneg gp.le _))⟩

/-- The original whole local Wick charge, its spatial rate, and all three Taylor errors are
bought together. The formal and the positive-coupling measurements use identical placements. -/
def Offer (b : Request G) (H : Patch) (K : KernelChoices) (x : ℝ):Prop:=
  ∃ (P : Oven H) (X : P.Form G) (C : ℝ),P.Offers X K ∧ X.Q=(b.2.2:ℝ)+1 ∧ 0≤C ∧
    C*|bond_fee (look false ∘ sight (first b)) (look false ∘ sight (second b)) X.Q (absolute b)|≤2+log x ∧
    (shade X)⁻¹ ≤ 2+log x ∧ Silk.Past X C (absolute b) (absolute b) (absolute b) ∧
    Income K X (first b) b.2.1 x ∧ Income K X (second b) b.2.1 x ∧ Income K X (together b) b.2.1 x

private theorem reserve (b : Request G) {H : Patch} {K : KernelChoices} (branches : H.Branches K G) :
    ∀ᶠ x : ℝ in atTop,Offer b H K x:=by
  obtain ⟨P⟩:=Oven.builtafter H
  obtain ⟨X,width,offer⟩:=P.fund branches ((b.2.2:ℝ)+1) (by positivity)
  obtain ⟨C,c₀,receipt⟩:=Silk.silence offer.good (absolute b) (absolute b) (absolute b)
  have grows:=tendsto_atTop_add_const_left _ (2:ℝ) tendsto_log_atTop
  let charge:=C*|bond_fee (look false ∘ sight (first b)) (look false ∘ sight (second b)) X.Q (absolute b)|
  filter_upwards [grows.eventually_ge_atTop charge,grows.eventually_ge_atTop (shade X)⁻¹,
    income offer (first b) b.2.1,income offer (second b) b.2.1,income offer (together b) b.2.1]
    with x fee rate a c joint
  exact ⟨P,X,C,offer,width,c₀,fee,rate,receipt,a,c,joint⟩

private theorem patches (b : Request G) (s : Sheet G) (D : Rolls s) (k : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ H : Patch,H.L=D.L k → H.J=k → Offer b H s.kernel x := by
  by_cases live : ∃ H : Patch,H.L=D.L k ∧ H.J=k
  · obtain ⟨H,h₁,h₂⟩:=live
    filter_upwards [reserve b (s.has H)] with x issued
    intro H' length date
    suffices H=H' from this ▸ issued
    cases H;cases H';dsimp only at *;grind
  exact Eventually.of_forall fun _ H length date=>False.elim (live ⟨H,length,date⟩)

def Paid (G : Gauge) : Prediction G:=fun {_} {_} {A} _=>∀b : Request G,∀ᶠ m : ℕ in atTop,
  Offer b (A.B.a.clock.op m 0).patch A.B.a.clock.kernel (A.B.a.clock.hatBeta m)

private theorem prepaid (s : Sheet G) (price : MapPrices) : Prepaid (@Paid G) s price:=by
  intro targets expenses flags program wages baton wants
  refine ⟨fun _=>0,?_⟩
  intro l hl D w u Z post scouts θ stages P V quarter
  letI:=Encodable.ofCountable (Request G)
  let demand (k : ℕ) (x : ℝ):Prop:=∀i : Fin (k+1),∀ b : Request G,Encodable.decode i=some b →
    ∀H : Patch,H.L=D.L k → H.J=k → Offer b H (ThroughLaunch.raise s l).kernel x
  have enough (k : ℕ) : ∀ᶠ x : ℝ in atTop,demand k x:=by
    apply eventually_all.mpr
    intro i
    rcases he : (@Encodable.decode (Request G) _ i) with _|b
    · filter_upwards with x u imp;contradiction
    · filter_upwards [patches b (ThroughLaunch.raise s l) D k] with x h b₁ eq
      rw [←Option.some.inj eq];exact h
  obtain ⟨W,hVW,_,grant⟩:=delay_extra V demand (fun _ _ _=>True) enough (fun _ _=>by simp)
  refine ⟨W,hVW,?_⟩
  intro U hWU table wait priced B
  dsimp only
  intro η q exchange aux rider booth b shelter works divides selection
  filter_upwards [B.a.fits.deep.eventually_ge_atTop (Encodable.encode selection)] with m later
  let k:=B.a.clock.J (m+1)
  let H:=(B.a.clock.op m 0).patch
  have side : H.L=D.L k:=Push.PriceCompiler.block_eq B.valid m
  rw [B.valid.kernel]
  exact (grant U hWU).1 k (B.a.clock.hatBeta m) (B.valid.pays m)
    ⟨Encodable.encode selection,Nat.lt_succ_of_le (later.trans (B.a.fits.mono (Nat.le_succ m)))⟩ selection
    (Encodable.encodek selection) H side rfl

/-- No final continuum field, period, ultraviolet date or desired pair is selected to obtain this income. -/
theorem allPrices : FundedPredictionSupply.AllPrices (@Paid G):=fun s _=>prepaid s _

end YM.Integration.WilsonMatrixTicketLanesConnectedBudget
