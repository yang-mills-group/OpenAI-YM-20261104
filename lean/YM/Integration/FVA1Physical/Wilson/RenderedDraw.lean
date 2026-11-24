import YM.Integration.FVA1Physical.Wilson.PortalPacket
import YM.Integration.FVA1Physical.Sources.Round2.CopiedPolynomial

/-! The whole incoming polynomial may have distributed support. The source cost
on a true normalized Schur draw is superalgebraic at every lattice volume. -/
set_option autoImplicit false
set_option maxHeartbeats 950000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Set Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Lis
open MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.Bakery.Film MSbar.Bakery MSbar.Bakery.Portal
open Push.Uniform MSbar.Measuring MSbar.Jade Next.SectorChange
open YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology BigOperators
variable {G:Gauge}

theorem packet_draw (m s p:ℕ) (h u:ℝ) :
    ∀ᶠ y:ℝ in atTop,∀ (A:Issue G) (V:Voice G) (_cle:Clear G V) (χ:ChartRatio G) (_hχ:LocalRatio χ)
      (b:Site A.f) (T:Nesting G A.f),BankPaid b y s p m h T →
      ∀ {g:ℝ},lensT y g → 0 < g → |g| ≤ 1 →
      ∀ (U:Config G A.f) (Z:Positions (Primary A.c G)) (lo hi K r δ:ℝ),lo ≤ hi →
      3*shade G*K < (LocalH.geom_patch G).choose → (mold A.pre A.F A.v).PosDef →
      let X:=boxX y b;let Y:=boxY y b;let O:=postcard G A.c g Z
      let ν:=vest (priced A.F A.v A.pre.clip A.pre.path) (g•Z)
      let cent:=sampleY A.F A.pre A.v V X Y U (g•Z) ∘ includeX A.F X
      Couch V A.F ν Y χ (linCash A.F (g•Z)) O lo hi K r δ →
      ∀ w∈clipM A.F X Y (hotel A.F X Y V O ν lo hi) χ g cent U,
      |clockReading p g T (chartLog g (canoe (S:=A.S) A.F (draw A.F X U cent g w)))-
        clockReading p g (enterRows A T) (meetVar Z (berth A.F A.pre A.v V X Y U Z g w))| ≤ y^u := by
  filter_upwards [rendered_packet_collar (G:=G) m s p h u] with y bound
  intro A V cle χ hχ b T bank g clock gp cap U Z lo hi K r δ pad small pd X Y O ν cent paid w hit
  have log:=copied_drawing_log A V cle χ hχ X Y (halo_subset ..) U gp Z lo hi K r δ small pd paid w hit
  rw [clockReading_enter,←log]
  exact bound A.S A.F V cle b O ν pad clock cap T bank _ hit.1

theorem packet_source_vault (A:Issue G) {m s p j:ℕ} {h a y:ℝ} (ha:0 ≤ a) (cool:a ≤ αm y)
    {b:Site A.f} (T:Nesting G A.f) (bank:BankPaid b y s p m h T) (σ:ℕ) (ij:j ≤ p) :
    Vault (address A.F G) {b} a s σ 0 (PowerSeries.coeff j (enterRows A T)) (enterFee G s^σ*y^h) ∧
        (PowerSeries.coeff j (enterRows A T)).totalDegree ≤ m := by
  have base:=Quote.cooled ha cool (bank.through σ ij)
  have bought:=enter_vault A s σ j ha {b} T 0 (by rw [Matrix.mulVec_zero];exact base)
  exact ⟨bought.1,bought.2.trans (bank j ij).1⟩

end YM.Integration.FVA1Physical.Wilson
