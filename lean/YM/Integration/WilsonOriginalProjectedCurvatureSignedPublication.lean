import YM.Integration.WilsonOriginalProjectedCurvaturePublishedCover

/-! The signed finite torus jet and its complete covered sum on the same marked club and dated card. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureSignedPublication
open Function Finset Filter Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn
open Org Push.PriceCompiler AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP PhysicalNext.Repeat.Boulevard
open AnalyticBridge VerifiedReset
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple)
  {V α ι KU:Type} [DecidableEq V] [Fintype V] [Countable ι] [Countable KU]
  (root:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (table:root.Tab R.rolls) (ψ:ℕ→ℕ) (books:Mentor.Offices.Books root R.rolls table ψ)
  (pass:Pass root table R.alloy R.kit)
  (education:Mentor.Educated root R.rolls table R.kit.shape R.kit.scout ψ books R.alloy.delay)
  {first m N per order:ℕ} {π:ℕ→Layout G} {Γ:ℕ→Pace.Coin}
  {H:(s:ℕ)→Rep G (R.family.side s per)}
local notation "J" => R.alloy.B.a.clock.J
variable (op:Mentor.Opportunity (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m))
  (epoch:Mentor.Epoch root R.rolls (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m) op)
  (card:WilsonMovingMentorItinerary.CardAt R root epoch.vac m)
  (journey:PlanV.Journey root R.alloy (N:=N) (m:=m) card) (upper:π (m+1)=card.extra)
  (course:Concourse R.alloy R.kit R.T π Γ first N per epoch.vac H)
  (start:first ≤ m) (before:m < N)
  {D:Passport (R.family.side (m+1) per) V} {ρ:Census V}
  (M:ι→Row D ρ G α) (w:V→ℝ) (positive:∀j,0<w j)
  (voter:Mentor.Cruise.Voter M (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (R.alloy.B.a.clock.J (m+1)))
    order op.count op.stage epoch.vac (R.alloy.B.a.clock.J m))
  (input:Tint.Incoming D (H (m+1)) α KU ρ) {b b':ℝ}
  (sealed:Travel.Seal (Tint.Patrol.picture M input) w b b') (y:α)


local notation "u" => (R.alloy.B.a.S.oneStep m per).exact_size
local notation "published" => (Mentor.Cruise.publish root R.rolls table R.alloy ψ books op epoch u M order voter card)
local notation "waist" => (Poetry.Agenda.waist root (Burn.horizon epoch.vac) (R.alloy.B.a.clock.J (m+1)))


open AllOrder AllOrder.Ink AllOrder.Fire AllOrder.Floe
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open QuadraticLocal.Sunrise Gauge Stationary Primitives.TwoWave RealSlice
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ink.Money

section
variable {S I₀:Type} [DecidableEq S] [Fintype S]
  {available:Side→Prop} {claims:S→Loan} {scale:I₀→ℝ} {occupied:Finset S}
  {rate:ℝ} {k l:ℕ} {filed:ℕ→I₀→Ink.Field (Coarse G⊕S)}
  {finite:ℕ→I₀→(n:Side) → rule (Coarse G⊕S) n→ℝ}

/-- Signed discrepancy of the precise finite input to the original painting, at one issued receipt. -/
def Assessed (_h:Aviary.Painted available claims scale occupied rate k l filed finite)
    (j:Fin (k+1)) (i:I₀) (terms:Fin (k+1)→Poetry.Roll G S): Prop:=
  ∃ c:ℝ, 0≤c ∧ ∀ n:Side,available n→∀ A:Link G n,∀ w:rule S n,
    |finite j i n (mingle A w) -
      ∑ t:Fin (k+1),((terms t).folded t.val j.val).table n (mingle A w)| ≤
      c*(1+|scale i|)^l*(n.val:ℝ)^l*dearth rate n*
        (1+‖mingle A w‖)^(Aviary.plusK claims occupied j.val+2)

private theorem invoice (h:Aviary.Painted available claims scale occupied rate k l filed finite)
    {terms:ℕ→I₀→Poetry.Roll G S} {anchor:S} {width:ℝ}
    (closed:Poetry.Agenda.Shelled occupied anchor claims filed terms scale l (k+1) width)
    (j:Fin (k+1)) (i:I₀):Assessed h j i (fun t=>terms t.val i):= by
  obtain ⟨f,⟨F,⟨c,hc,hF⟩,hf⟩,sell⟩:=h.earned j (by omega)
  refine ⟨c,hc,?_⟩
  intro n hn A w
  have read:=(sell i n hn).2.2 (mingle A w)
  change |finite j i n (mingle A w)-(filed j i).table n (mingle A w)| ≤ _ at read
  rw [closed.recollects j j.isLt i n A w] at read
  rw [←Fin.sum_univ_eq_sum_range] at read
  refine read.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact mul_le_mul_of_nonneg_right ((hf i n).2.trans
    (mul_le_mul_of_nonneg_right (hF i).2 (by positivity))) (Real.exp_nonneg _)
end

local notation "J₀" => R.alloy.B.a.clock.J
local notation "tin" C:max=> Mentor.Cruise.ticket root R.rolls R.alloy ψ op epoch M C order voter
local notation "slots" C:max=> Mentor.Cruise.rules root R.rolls R.alloy ψ op epoch u M C order voter
local notation "roster" C:max=> books.lore (J₀ (m+1)) (J₀ m) op epoch (tin C)
local notation "arrival" C:max=> Mentor.artifact root R.rolls R.alloy ψ op epoch (tin C) (slots C) card

omit [Countable ι] in
/-- The deposited card identifies the finite sampler and every folded term in the received edition. -/
theorem original (C:Earn.Club M) (j:Fin (order+1)):
    Assessed (roster C).ledger.reads j (arrival C) ((published).news C):= by
  exact invoice (roster C).ledger.reads (roster C).ledger.shells j (arrival C)

end YM.Integration.WilsonOriginalProjectedCurvatureSignedPublication
