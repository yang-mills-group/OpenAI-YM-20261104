import YM.Integration.WilsonLimitConstruction.FundedOriginalRun
import YM.WilsonCoeffUV.Emit.Cumulative
import YM.WilsonCoeffUV.Product.Report.Family

/-! Purchase the genuine rooted cover program during the original native
company's two-stage choice. The resulting realm has the levels and chart of
the very same Run that supplies the finite independent Wilson coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FundedMarkedCoverRows
open Function Filter Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonLimitConstruction
open scoped Topology

universe u
variable {G : Gauge}

/-- Four numerical purchases on the stored sheet and the stored rolls.
The early prices use no chosen block, and the late prices use no chosen
geometry, cutoff, torus period, source or test. -/
def prices (v : ℕ → Gear G → ℝ) : FundedCompanySelection.Prediction G :=
  fun {M} {D} {A} _ => M.O = chart G ∧
    horiz (hol G) (primes G) (chart G) id M.p.kernel ≤ M.p.floorL ∧
    preBoard M.p id ≤ M.p.floorL ∧
    aperture (hol G) (primes G) (chart G) id D ≤ A.delay.betaEntry ∧
    coolTax id M.p D (chart G) (diary G ⊔ v) ≤ A.delay.betaEntry

/-- Select the two concrete prices in their original order, allowing every
later enlargement by another prediction. -/
theorem purchase (v : ℕ → Gear G → ℝ) :
    FundedPredictionSupply.AllPrices (@prices G v) := by
  intro s quote targets expenses chartEq programs wages baton valid
  let floor := horiz (hol G) (primes G) (chart G) id s.kernel ⊔ preBoard s id
  refine ⟨floor, ?_⟩
  intro l hl D w U reg post scouts θ stages cost V quarter
  let kernelFees := aperture (hol G) (primes G) (chart G) id D
  let markFees := coolTax id (ThroughLaunch.raise s l) D (chart G) (diary G ⊔ v)
  let next : Delays θ := { V with betaEntry := (kernelFees ⊔ markFees) ⊔ V.betaEntry }
  refine ⟨next, ⟨le_sup_right, le_rfl, le_rfl, le_rfl⟩, ?_⟩
  intro W' hW bar wait priced B0
  dsimp only
  intros
  exact ⟨rfl, le_sup_left.trans hl, le_sup_right.trans hl,
    (le_sup_left.trans le_sup_left).trans hW.beta,
    (le_sup_right.trans le_sup_left).trans hW.beta⟩

/-- Financial and rooted-operator conclusions for every finite named marker
request on an already selected original priced Run. -/
theorem realm (R : Run G) (hG : G.Simple) (v : ℕ → Gear G → ℝ)
    (paid : prices v R.kit) (n : ℕ) (k D : Fin n → ℕ) (hk : ∀ i, k i < D i)
    (e b h : ℕ) : ∀ᶠ m : ℕ in atTop,
    ∃ Q : Realm G (e+1) Credit.leanC, Q.draws = R.family.path.levels ∧
      Q.paid = R.metals.O ∧ Q.y = zz R.family.path.levels ∧ Q.anchor = m ∧
      Cloze D k Q Credit.leanC ∧ Insure b h Q Credit.leanC ∧
      Nonempty (Tribe Q (hol G) Credit.leanC Credit.leanC (counter (hol G) (primes G) k D hk)) ∧
      ∀ j, m ≤ j → ∀ hj : Q.anchor ≤ j, ∃ z : 5 ≤ R.family.path.levels.clock.J (j+1),
        (Q.mint j hj).σ = crestM R.family.path.levels j z ∧
        v (R.family.path.levels.clock.J (j+1)) (Q.mint j hj).gear ≤ Q.cash Credit.leanC j := by
  obtain ⟨chartEq, hfloor, hwidth, hkernel, hmark⟩ := paid
  have awards := reported (hol G) (primes G) hfloor hkernel
  rw [chartEq]
  exact maturity (hol G) (primes G) hk hG (chart_ok G) awards.ink awards.rise
    hwidth R.alloy.B.valid awards.fg awards.hg v hmark tendsto_id b h e

/-- The cover issuer and an arbitrary partner purchase are carried by one
original Run and its own finite reconstruction. -/
theorem original (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) (v : ℕ → Gear G → ℝ)
    (P : FundedCompanySelection.Prediction G) (hP : FundedPredictionSupply.AllPrices (@P)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      prices v R.kit ∧ P R.kit ∧ NativeFVAPlateau.Correlations R ∧
      FundedOriginalProperties.{u} hG ε W := by
  obtain ⟨R, T, W, hp, hcor, hfund⟩ := fundedOriginalRun_with_prediction.{u} hG hε
    (@FundedPredictionSupply.Both G (@prices G v) (@P))
    (fun s q => FundedPredictionSupply.both (purchase v s q) (hP s q))
  exact ⟨R, T, W, hp.1, hp.2, hcor, hfund⟩

end YM.Integration.FundedMarkedCoverRows
end
