import YM.Integration.WilsonReceivedChronologicalFixedRosePhysicalMesh
import YM.Integration.WilsonOriginalObservedRosePublicCurrency
import YM.Integration.WilsonOlderFreshSoftSocketStationPanelCapital

/-! Convert both genuine public socket sums at the elected physical K into older currency. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseFittedCurrency
open Function Filter Finset Lattice Wilson RG PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketMeasuredCash (packet)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple){n:ℕ}
local notation "H" => R.family.path.levels.clock.hatBeta

private theorem convert {a b z u t:ℝ}{e E:ℕ}(eb:e≤E)(up:0≤u)(one:1≤b)(zp:0≤z)
    (native:b^E≤(4:ℝ)^E*t^(2*E))(paid:a≤u*b^e*z):
    a≤(u*(4:ℝ)^E)*t^(2*E)*z:=by
  calc _ ≤ u*b^e*z:=paid
       _ ≤ u*((4:ℝ)^E*t^(2*E))*z:=mul_le_mul_of_nonneg_right
         (mul_le_mul_of_nonneg_left ((pow_le_pow_right₀ one eb).trans native) up) zp
       _ = _:=by ring

include simple in
theorem original (L E:ℕ)(d:Fin n→ℕ):
    ∀ᶠ v:ℕ in atTop,∀{K N per:ℕ},v≤K → K≤N →
      R.family.S.scale K-R.family.S.scale v≤L*Real.log (H v) →
      ∀s:Finset (Fin n),∀w:(i:Fin n)→R.family.label (d i),∀r:ℝ,∀h mesh e f:ℕ,e≤E → f≤E →
        ∀M C:ℝ,0≤M → 0≤C →
        let z:=(regulatorRun R.family N per v)⁻¹
        let cost:=z^(mesh*h+1)
        let sumW:=∑q:Selection R d s,‖weight R d N per K w s q‖
        let sumP:=∑q:Columns R (fun i:s=>d i.val),‖packet R d s w N per K q‖
        r^h*sumW≤M*(H K)^e*cost → r^h*sumP≤C*(H K)^f*cost →
          r^h*sumW≤(M*(4:ℝ)^E)*z^(2*E)*cost ∧
          r^h*sumP≤(C*(4:ℝ)^E)*z^(2*E)*cost:=by
  filter_upwards [WilsonOriginalObservedRosePublicCurrency.clock R simple L E]
    with v desk K N per vk kn span s w r h mesh e f eb fb M C mp cp
  dsimp only
  intro income terminal
  have g0:0≤(regulatorRun R.family N per v)⁻¹:=inv_nonneg.mpr
    (ActualRunKernelPackets.regulator_pos R N per v (vk.trans kn)).le
  have gate:=desk N per K vk kn span
  have hk:1≤H K:=(R.family.path.levels.fits.delayed K).le
  exact ⟨convert eb mp hk (pow_nonneg g0 _) gate income,convert fb cp hk (pow_nonneg g0 _) gate terminal⟩

end YM.Integration.WilsonReceivedChronologicalFixedRoseFittedCurrency
