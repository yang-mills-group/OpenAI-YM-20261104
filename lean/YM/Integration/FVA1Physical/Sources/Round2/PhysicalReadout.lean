import YM.Integration.FVA1Physical.Sources.Round2.RetainedGas
import YM.Integration.FVA1Physical.Sources.Round2.MarkerSlope
import YM.Integration.FVA1Physical.Sources.Round2.PhysicalPrice

/-! All-configuration physical readout when replacing the regular exponent
and retaining the actual masked marked gas. -/

namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics

open MeasureTheory Lattice RG Wilson RG.Supply Input Org Source Extra.Histories LocalLTE LocalLTE.Sail
open MergeProof MergeProof.Accent YM.Integration.FVA1Physical YM.Integration.FVA1Physical.Round2
open ConnectedActivityE6
open scoped BigOperators

variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} {P : Bolt A}
variable {N n i : ℕ} {I : Type} [DecidableEq I] [Fintype I]
variable (B : Marker.Census I) (Y : Batch (Issue.trail P) N n I)
variable (π : ∀ j : ℕ, j ≤ N → Y.steering j)
variable (F : ∀ (j : I) (s : ℕ), ((Labels.frames G).level (Y.demand j)).Coeff →
  Coefficient ((Labels.frames G).level (Y.demand j)) ((Issue.trail P).S.side s n))
variable (hi : i < N) (O : Appendix B ((Issue.trail P).rep N n i))
variable (V : ∀ d, Music ((Labels.frames G).level d) (Issue.trail P) N n)

/-- Forecast at every coarse configuration, with the C18 regular field, the
actual singleton and mixed forced entries, and the original vacuum exponent. -/
noncomputable def gasForecast :=
  Sail.Round2.retainedForecast B ((Issue.trail P).rep N n i) O (spectralValue Y π F hi)
    (fun j => (Y.named V (π i hi.le) j).forced)

noncomputable def gasReadoutCost (p K : ℕ) : ℝ :=
  let t := (2 * K) * Coat.gStep ((Issue.trail P).rep N n (i + 1)).beta ^ ((p : ℝ) + 1)
  stencilInsertionBound (Issue.trail P) N Y.demand Y.voice * (markerSlope (Fintype.card I) t * t)

/-- All joint coefficients, including mixed entries, at configurations with
arbitrary flags. Only the regular exponent has been changed. -/
theorem physicalRetainedPrice {p K : ℕ} (h : ∀ v, FinePrint V B Y π F hi O p K v)
    (hp : Appendix.Prepared B ((Issue.trail P).rep N n i) O (Y.origin i) (Y.requested V i)
      (fun j => (Y.named V (π i hi.le) j).forced) (gust (Issue.trail P) N n N (Y.raw B) i hi.le))
    (v : Config G ((Issue.trail P).S.side i n)) :
    Marker.Poly.price (fun _ => 1)
      (gasForecast B Y π F hi O V v - gust (Issue.trail P) N n N (Y.raw B) i hi.le v) ≤
        ((Issue.trail P).rep N n i).eval v * gasReadoutCost (i := i) Y p K := by
  let H := Issue.trail P
  let raw := gust H N n N (Y.raw B) i hi.le v
  let receipt := Sail.receipt B O (Y.requested V i) v
  let forecast := Sail.forecast B O (spectralValue Y π F hi) v
  let t := (2 * K) * Coat.gStep (H.rep N n (i + 1)).beta ^ ((p : ℝ) + 1)
  let δ := forecast - receipt
  have hf := h v
  have hδ : Marker.Poly.price (fun _ => 1) δ ≤ t := by
    have e : δ = (-1 : ℂ) • (receipt - forecast) := by simp [δ]
    rw [e, Marker.Poly.adapted, norm_neg, norm_one, one_mul]
    exact hf.log
  have hfactor := Sail.Round2.retainedForecast_eq B (H.rep N n i) O (Y.origin i)
    (Y.requested V i) (spectralValue Y π F hi) _ _ hp v hf.vote.1 hf.vote.2
  change Marker.Poly.price (fun _ => 1) (gasForecast B Y π F hi O V v - raw) ≤ _
  rw [show gasForecast B Y π F hi O V v = raw * Marker.Poly.pass δ from hfactor,
    show raw * Marker.Poly.pass δ - raw = raw * (Marker.Poly.pass δ - 1) by ring]
  apply (Marker.Poly.multiplication (fun _ => zero_lt_one) _ _).trans
  have hraw := coarsePhysicalPrice P.choice B Y i hi.le v
  exact (mul_le_mul hraw (price_pass_sub_one δ hδ) (Marker.Poly.nonnegative
    (fun _ => zero_lt_one) _) ((Marker.Poly.nonnegative (fun _ => zero_lt_one) raw).trans hraw)).trans_eq
      (mul_assoc ..)

end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
