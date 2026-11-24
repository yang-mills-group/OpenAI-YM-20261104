import YM.Integration.WilsonOrdinaryNestedMSPoint

/-! Transport of ordinary OPE coefficients on the same complete continuum
correlation arrays. Uniqueness against the full exterior family moves the
output, including the unit. A dimensional change of representatives can
use a series-valued matrix. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorOPE
open Function Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open FVA2.O FVA2.O.Score FVA2.O.Project FVA2.O.Enh FVA2.O.Bind FVA2.O.Read
open MS MS.Land MS.Fleet MS.Theater
open scoped Classical BigOperators
variable {G : Gauge}

theorem determined {A B : Arenas G} {pA pB : ℝ → Book.Program.Cn}
    {ZA ZB : ℝ → Frames G} (ha : Canon.Physical A pA ZA) (hb : Canon.Physical B pB ZB)
    (q : Book.Program.Cn) (hq : Book.Program.Rooted q)
    (T V : Cast G) (invert : V*T=1)
    (readings : ExchangeA q T (install A) = install B) {n : ℕ} (u : Scan G n) (r : ℝ) :
    Canon.Gift_shape T q u (fun v => Canon.OPECoefficients A v r) (Canon.OPECoefficients B u r) := by
  have transported : Canon.LogPricing B u = holding q T V (Canon.LogPricing A) u := by
    apply hb.unique
    rw [← readings]
    exact paid_w hq invert ha.works
  intro x
  apply Gift.total hq
  rw [transported]
  exact rate invert

/-- The two MS calculations use the prescribed dimensional plot.
The correlation comparison is on their actual renormalized physical arrays.
At fixed positive orientation the formal coupling here is the identity. -/
theorem recorded (Z : WilsonPrescription G) (hG : G.Simple)
    (M M' : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν : ℝ)
    (T V : Cast G) (invert : V*T=1)
    (rows : marking T (install (Equator.wave ν M)) = install (Equator.wave ν M'))
    {n : ℕ} (u : Scan G n) (r : ℝ) :
    Canon.Gift_shape T PowerSeries.X u (fun v => Canon.OPECoefficients (Equator.wave ν M) v r)
      (Canon.OPECoefficients (Equator.wave ν M') u r) := by
  obtain ⟨_,s⟩ := Main.wilson_to_MS Z hG M false
  obtain ⟨_,s'⟩ := Main.wilson_to_MS Z hG M' false
  apply determined (s.separatedOPE ν).continuum (s'.separatedOPE ν).continuum
    PowerSeries.X (by simp [Book.Program.Rooted]) T V invert
  have h : tune PowerSeries.X (install (Equator.wave ν M)) = install (Equator.wave ν M) := by
    funext k x i
    exact PowerSeries.X_subst _
  simpa only [ExchangeA, h] using rows

end YM.Integration.WilsonSurveyedColorOPE
end
