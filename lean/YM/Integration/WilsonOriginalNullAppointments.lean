import YM.Integration.WilsonOriginalNullWrappedFee
import YM.Integration.WilsonOriginalNullContraction
import YM.Integration.WilsonOriginalNullFlatPrimary

/-! All appointments for the null comparison on the measured original run are
fixed before period, cutoff, site and the numerical upper input. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullAppointments
open Filter Labels Lattice Wilson RG Source Trace.Physical Trace.Physical.Germ
open PhysicalNext Repeat Legato Graces Roost Org Push.Local Extra.Histories Next.Foundations
open scoped Classical Topology
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "F₀" => R.family.labels.level d
local notation "T₀" => R.family.localSection d
local notation "B₀" j:max => R.family.path.levels.budget j
local notation "w₀" j:max => price G (max (B₀ j).order (B₀ j).power)
local notation "staff₀" j:max => factor R.family.params T₀ (B₀ j).supportExponent (w₀ j)
local notation "block₀" j:max => GermGraph.factor R.family j
local notation "stock₀" j:max => 2 + 4*(R.family.path.levels.params j).columns

structure Paid (i:ℕ) : Prop where
  lower : WilsonOriginalNullContraction.Ready R i d
  upper : WilsonOriginalNullContraction.Ready R (i+1) d
  reserve : 4*(stock₀ i)*(block₀ i)^(-(2/5:ℝ)) ≤ (block₀ i)^(-(1/8:ℝ))
  wrapped : ∀ (per:ℕ) (U:Rep G (R.family.side (i+1) per)), U.p=B₀ (i+1) →
    ∀ (o:Site (R.family.side (i+1) per))
      (h:Coefficient F₀ (R.family.side (i+1) per)) {κ b:ℝ}, h.Format o R.family.params U →
      h.remBound o U κ b → projection F₀ R.family.params U.p.threshold o h=0 →
      let wage := price G (max U.p.order U.p.power)
      let fee := (block₀ i)^d*(4*staff₀ i+1)*U.p.mass ((T₀).footprint o) (wage*(F₀).coeffSize h.x)
      4*(stock₀ i)*fee ≤ (block₀ i)^(-(1/8:ℝ))*b

theorem original (simple:G.Simple) (M:WilsonMeasuredRankedMenu.Menu R d)
    (slow:WilsonWindowReportingPace.Slow R.kit)
    (roster:∀ j,j ≤ (R.metals.p.profile j).order ∧ j ≤ (R.metals.p.profile j).power) :
    ∀ᶠ i:ℕ in atTop, Paid R d i := by
  have clocks:=WilsonOriginalNullContraction.eventual R simple slow roster d
  obtain ⟨lower,hclock⟩:=eventually_atTop.mp clocks
  obtain ⟨upper,hwrap⟩:=eventually_atTop.mp (WilsonMeasuredNullWrappedDate.original R simple d (-((d:ℝ)+6)))
  filter_upwards [eventually_ge_atTop lower,eventually_ge_atTop upper,
    WilsonOriginalNullStock.original R.family,WilsonOriginalNullWrappedFee.original R d M]
    with i arrive next stock priced
  have fine:=hclock (i+1) (Nat.le_succ_of_le arrive)
  refine ⟨hclock i arrive,fine,stock,?_⟩
  intro per U point o h κ b shape paid null wage fee
  have du : d ≤ U.p.order := point.symm ▸ fine.2.2.1
  have pu : d ≤ U.p.power := point.symm ▸ fine.2.2.2.1
  have held:=hwrap (i+1) (Nat.le_succ_of_le next) per U point o h shape paid du pu null
  dsimp only [fee,wage]
  rw [point]
  exact priced per o h.x b (rem_nonneg paid) held

end YM.Integration.WilsonOriginalNullAppointments
