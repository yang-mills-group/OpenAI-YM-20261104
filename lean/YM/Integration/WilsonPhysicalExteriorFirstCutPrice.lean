import YM.Integration.WilsonPhysicalExteriorFundedPeriod
import YM.Integration.WilsonPhysicalExteriorFirstCut
import YM.Integration.WilsonPhysicalExteriorFirstCutScale

/-! The funded physical field book and independent MS datum on both genuine
finite sides. The first ultraviolet and far stops come from the same Wilson
run. The original Lodge notebook and its terminal independent-period price use
exactly the prescription used for these first-cut rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorFirstCutPrice
open Filter Real Lattice RG RG16 PhysicalNext.Repeat.Legato
open MS MS.Dial MS.Menus MS.Land MS.Rake MS.Tide MS.Fleet
open FVA2 Register YM.FVAAlt2 Precision RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Lodge
open WilsonPhysicalExteriorActualSides WilsonPhysicalExteriorResolvedCutoff
open WilsonPhysicalExteriorUVStory WilsonPhysicalExteriorFirstCut
open scoped Topology Classical

variable {G:Gauge} (R:Run G)
local notation "B₀" => Press.portDeck G
local notation "M₀" => MS_Data G (Position.OpenAxis.Plot B₀)
local notation "Y₀" => Oracle.books R.family.path.levels.clock.kernel
local notation "Λ₀" => RG16.Lambda R.family.path.levels

def Rows (M:M₀) (Q:Prescription B₀) : Prop :=
  ∀ (n:ℕ) (D:Fin n→Label B₀) (c c':ℝ) (W:Fin n→ℕ→ Cover)
    (_:∀m:ℕ,((R.family.S.block m).val:ℝ)≤log (Λ₀ m))
    (_:1<c') (_:c'<c) (_:c<2) (lo:ℕ→ℕ)
    (_:Reach (geometry R c 0) (field R c 0 W).off)
    (_:Resolved (geometry R c 0) (info (field R c 0 W).off))
    (μ q:ℝ) (k h:ℕ),
    ∀ᶠ j:ℕ in atTop,∀ side:Bool,∀ per≥floor R c lo j,
      let T:=WilsonPhysicalExteriorFirstCutScale.ratio R c' j
      let amount:=fun u:ℝ=>T^h*‖signed R M Q D c W side k u (j,per)‖
      amount μ≤exp (-q*Λ₀ j) ∧ amount (μ+R.family.S.scale j)≤exp (-q*Λ₀ j)

theorem first (hG:G.Simple) {M:M₀} (Q:Prescription B₀)
    (hQ:TaylorOKPl M (Lobby.Table (basisR R) B₀) Q) : Rows R M Q := by
  intro n D c c' W slow h₁ h₂ h₃ lo reach apart μ q k h
  apply Filter.eventually_all.mpr
  intro side
  obtain ⟨A,hA,d,correct⟩:=corrected R M Q D c W hG slow (h₁.trans h₂).le h₃
    lo reach apart hQ side k
  have held:=WilsonPhysicalExteriorFirstCutScale.at_fixed R hG (h₁.trans h₂) h₂
    slow μ A q hA d h
  have moving:=WilsonPhysicalExteriorFirstCutScale.paid R hG (h₁.trans h₂) h₂
    slow μ A q d h
  filter_upwards [correct,held,moving] with j hj fixed moved per hp
  have nonnegative:0≤(WilsonPhysicalExteriorFirstCutScale.ratio R c' j)^h :=
    pow_nonneg (exp_pos _).le h
  exact ⟨(mul_le_mul_of_nonneg_left (hj per hp μ) nonnegative).trans fixed,
    (mul_le_mul_of_nonneg_left (hj per hp (μ+R.family.S.scale j)) nonnegative).trans moved⟩

theorem funded {hG:G.Simple} (N:WilsonPrescription G) {M:M₀} {S:Prescription B₀}
    {dial:Bool} (matchMS:Main.Match N hG M S dial)
    (purchase:NativeFVAPlateau.Correlations R) :
    ∃ (Z:∀ b:Patch,b.Branches R.family.path.levels.clock.kernel G)
      (ledger:Lodge.Contract R Y₀ Z) (Q:Prescription B₀),
      Q.team=S.team ∧ TaylorOKPl M (Lobby.Table (basisR R) B₀) Q ∧
        WilsonPhysicalExteriorFundedPeriod.Periods R Z ledger Q ∧ Rows R M Q := by
  obtain ⟨Z,ledger,Q,team,taylor,periods⟩:=
    WilsonPhysicalExteriorFundedPeriod.on_run R N matchMS purchase
  exact ⟨Z,ledger,Q,team,taylor,periods,first R hG Q taylor⟩

end YM.Integration.WilsonPhysicalExteriorFirstCutPrice
end
