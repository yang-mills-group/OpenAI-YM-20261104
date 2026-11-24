import YM.Integration.WilsonMatrixTicketLanesReportedWords
import YM.Integration.WilsonLimitConstruction.FundedPredictionSupply
import YM.RGComparison.Core16.Spool.Transfer
import YM.Push.PRICE_COMPILER.Scene
import YM.Push.PRICE_COMPILER.Post

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedPrepaid
open Function Filter Set Finset Real Lattice RG Wilson Tree Precision RG.Supply
open PhysicalNext PhysicalNext.Repeat ThroughLaunch Next.Foundations Push.PriceCompiler Input
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Parcel
open RGComparison.Core16.Forge RGComparison.Core16.Lumen
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection WilsonMatrixTicketLanesReportedWords
open scoped Topology Classical BigOperators
variable {G : Gauge}

def start : Lumen.Stage := ⟨1,0,le_rfl⟩

/-- The original operational reserve for one globally enumerated marked word. -/
def Offer (b : Menu G) (H : Patch) (K : KernelChoices) (x : ℝ) : Prop :=
  ∃ (P : Oven H) (X : P.Form G) (U : Lumen.Stage) (C : ℝ),
    P.Offers X K ∧ X.Q=((b.2.2:ℝ)+1) ∧ U.Above start ∧ 0 ≤ C ∧ C ≤ 2+log x ∧
    (sqrt (x/2))⁻¹ ≤ dollar U.L ∧ ∀ (c f : Side) (size : f.val=c.val*H.L.val),
      let S : StepData c f := ⟨H,K,size⟩
      Bid.Larger (G:=G) S → ∀ (T : Forest S.ratio) (u : Directions G c) (o : Fin b.1.1 → Site f),
      (∀ i, ‖u i‖ ≤ (b.2.2:ℝ)+1) → Spool.Price U b.2.1 C
        (Spool.rank (fun i=>lamp (b.1.2 i)) S T X (chart G) u o)
        (Spool.reads (fun i=>lamp (b.1.2 i)) S u o)

private theorem reserve (b : Menu G) {H : Patch} {K : KernelChoices} (branches : H.Branches K G) :
    ∀ᶠ x : ℝ in atTop,Offer b H K x := by
  obtain ⟨P⟩ := Oven.builtafter H
  obtain ⟨X,cap,accept⟩ := P.fund branches ((b.2.2:ℝ)+1) (by positivity)
  obtain ⟨U,C,wider,C0,all⟩ := Spool.every (fun i=>lamp (b.1.2 i)) accept start b.2.1 (chart_ok G)
  have heat : Tendsto (fun x : ℝ => (sqrt (x/2))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_sqrt_atTop.comp (tendsto_id.atTop_div_const zero_lt_two))
  filter_upwards [heat.eventually (gt_mem_nhds (dollar_pos U.L)),
    (tendsto_atTop_add_const_left _ (2:ℝ) tendsto_log_atTop).eventually_ge_atTop C] with x small front
  refine ⟨P,X,U,C,accept,cap,wider,C0,front,le_of_lt (show _<dollar U.L from small),?_⟩
  intro c f size S big T u o seated
  exact all c f size big T u o (cap.symm ▸ seated)

private theorem patches (b : Menu G) (s : Sheet G) (D : Rolls s) (k : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ H : Patch,H.L = D.L k → H.J = k → Offer b H s.kernel x := by
  by_cases live : ∃ H : Patch,H.L=D.L k ∧ H.J=k
  · obtain ⟨H,same,stage⟩ := live
    filter_upwards [reserve b (s.has H)] with x issued
    intro H' length date
    suffices H=H' from this ▸ issued
    cases H
    cases H'
    dsimp only at *
    grind
  exact Eventually.of_forall fun _ H length date => False.elim (live ⟨H,length,date⟩)

/-- A single prediction chosen before the original campaign reaches every
word in every marked physical input roster, with all future volumes in each offer. -/
def Paid (G : Gauge) : Prediction G := fun {_} {_} {A} _ =>
  (∀ i p,Bid.Larger (G:=G) (A.B.a.clock.op i p)) ∧
    ∀ b : Menu G,∀ᶠ m : ℕ in atTop, Offer b (A.B.a.clock.op m 0).patch
      A.B.a.clock.kernel (A.B.a.clock.hatBeta m)

theorem prepaid (s : Sheet G) (price : MapPrices) : Prepaid (@Paid G) s price := by
  intro targets expenses flags program wages baton wants
  refine ⟨fun _ => 0,?_⟩
  intro l hl D w u Z post scouts θ stages P V quarter
  letI := Encodable.ofCountable (Menu G)
  let demand (n : ℕ) (x : ℝ) : Prop := ∀ i : Fin (n+1),∀ b : Menu G,Encodable.decode i = some b →
    ∀ H : Patch,H.L = D.L n → H.J = n → Offer b H (ThroughLaunch.raise s l).kernel x
  have enough (n : ℕ) : ∀ᶠ x : ℝ in atTop,demand n x := by
    apply eventually_all.mpr
    intro i
    rcases he : (@Encodable.decode (Menu G) _ i) with _|b
    · filter_upwards with x u imp; contradiction
    · filter_upwards [patches b (ThroughLaunch.raise s l) D n] with x promised u eq
      rw [←Option.some.inj eq]
      exact promised
  let VB : Delays θ := { V with shells := fun i => max (V.shells i) (macroNeed D i) }
  have first : DelayLe V VB := ⟨le_rfl,le_rfl,fun _=>le_max_left ..,le_rfl⟩
  obtain ⟨W,hVW,_,grant⟩ := delay_extra VB demand (fun _ _ _=>True) enough (fun _ _=>by simp)
  refine ⟨W,first.trans hVW,?_⟩
  intro U hWU table wait priced B
  dsimp only
  intro η q exchange aux rider booth b shelter works divides
  have space : macroNeed D ≤ U.shells :=
    (show macroNeed D ≤ VB.shells from fun _=>le_max_right ..).trans (hVW.trans hWU).shells
  refine ⟨larger_paid space B.valid,?_⟩
  intro b
  filter_upwards [B.a.fits.deep.eventually_ge_atTop (Encodable.encode b)] with m later
  let k := B.a.clock.J (m+1)
  let H := (B.a.clock.op m 0).patch
  have side : H.L=D.L k := Push.PriceCompiler.block_eq B.valid m
  rw [B.valid.kernel]
  exact (grant U hWU).1 k (B.a.clock.hatBeta m) (B.valid.pays m)
    ⟨Encodable.encode b,Nat.lt_succ_of_le (later.trans (B.a.fits.mono (Nat.le_succ m)))⟩ b
    (Encodable.encodek b) H side rfl

theorem allPrices : FundedPredictionSupply.AllPrices (@Paid G) := fun s _ => prepaid s _

end YM.Integration.WilsonMatrixTicketLanesReportedPrepaid
