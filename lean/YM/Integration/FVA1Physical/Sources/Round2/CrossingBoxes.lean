import YM.Integration.FVA1Physical.Sources.Round2.RetainedGas

/-! On a healthy anchor region, a nonzero marked forced box joins a source
site to a flag outside that region. Vacuum boxes may still be anywhere. -/

namespace YM.LocalLTE.Sail.Round2

open Lattice RG Wilson Source Marker MergeProof MergeProof.Accent
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {I : Type} [DecidableEq I] [Fintype I]

private theorem profileSites {d : ℕ} {F : Labels.Frame G d} (R : Rep G n)
    (W : Coefficient F n) {o : Site n} {a : Hol G} (h : W.Format o a R) (U : Config G n)
    (e : Box n) (he : profile R.activities W.forced e U ≠ 0) :
    o ∈ e.1 ∧ ∃ z ∈ e.1, z ∈ flags R.p.threshold U := by
  obtain ⟨k, hk⟩ : ∃ k : {k // barcode R.activities k = e}, W.forced k.val U ≠ 0 := by
    by_contra! hzero
    exact he ((tsum_congr hzero).trans tsum_zero)
  have hsup : (R.activities.forced k.val).support = e.1 := congrArg Prod.fst k.property
  have hcar := h.carried k.val (fun hzero => hk (congrFun hzero U))
  obtain ⟨z, hz⟩ := (R.activities.forced k.val).inventory_ne
  have hin := Finset.mem_inter.mp (((h.forcing k.val U hk).1).symm ▸ hz)
  exact ⟨hsup ▸ hcar, z, hsup ▸ hin.1, hin.2⟩

omit [Fintype I] in
private theorem mixedSites (B : Census I) (o : I → Site n) {t : ℝ} (e : Box n)
    (F : Config G n → Poly B) (h : Flow o e F t) (hr : ∀ U, rises (F U)) (U : Config G n)
    (hF : F U ≠ 0) : (∃ j, o j ∈ e.1) ∧ ∃ z ∈ e.1, z ∈ flags t U := by
  obtain ⟨s, hs⟩ : ∃ s, (F U).part s ≠ 0 := by
    by_contra! hz
    apply hF
    ext s
    exact hz s
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) (hr U s hs))
  obtain ⟨hmask, hz, _⟩ := h.permits U hF
  obtain ⟨z, h'⟩ := hz
  have hin := Finset.mem_inter.mp (hmask.symm ▸ h')
  exact ⟨⟨j, h.toBorne.place s U hs (Finset.mem_image_of_mem o hj)⟩, z, hin.1, hin.2⟩

def crossingBox (o : I → Site n) (A : Support n) (e : Box n) : Prop :=
  (∃ j, o j ∈ e.1) ∧ ∃ z ∈ e.1, z ∉ A

theorem crossing_or_zero (B : Census I) (R : Rep G n) (O : Appendix B R) (o : I → Site n)
    {a : Hol G} {d : I → ℕ} {L : ∀ j, Labels.Frame G (d j)}
    (W : ∀ j, Coefficient (L j) n) (hW : ∀ j, (W j).Format (o j) a R)
    (hO : Carton o O.H O.K R.p.threshold) (A : Support n) (U : Config G n)
    (hA : Healthy R.p.threshold A U) (e : Box n) (he : ¬ crossingBox o A e) :
    Mach B (fun j => profile R.activities (W j).forced e U) + O.K e U = 0 := by
  have hx (hj : ∃ j, o j ∈ e.1) (hz : ∃ z ∈ e.1, z ∈ flags R.p.threshold U) : False := by
    obtain ⟨z, hmem, hflag⟩ := hz
    exact he ⟨hj, z, hmem, fun h => (Finset.disjoint_left.mp hA) h hflag⟩
  have hp (j : I) : profile R.activities (W j).forced e U = 0 := by
    by_contra hn
    obtain ⟨h₀, h'⟩ := profileSites R (W j) (hW j) U e hn
    exact hx ⟨j, h₀⟩ h'
  have hm : O.K e U = 0 := by
    by_contra hn
    obtain ⟨h₀, h'⟩ := mixedSites B o e (O.K e) (hO.flag e).1 (hO.flag e).2 U hn
    exact hx h₀ h'
  simp [Mach, hp, hm]

/-- In the healthy anchor sector only crossing boxes require an identification
of the marked forces. Vacuum polymer factors have been retained exactly. -/
theorem retainedForecast_crossing (B : Census I) (R : Rep G n) (O : Appendix B R) (o : I → Site n)
    {a : Hol G} {d : I → ℕ} {L : ∀ j, Labels.Frame G (d j)}
    (W : ∀ j, Coefficient (L j) n) (hW : ∀ j, (W j).Format (o j) a R)
    (hO : Carton o O.H O.K R.p.threshold) (A : Support n) (U : Config G n)
    (hA : Healthy R.p.threshold A U) (F : I → Config G n → ℂ) :
    retainedForecast B R O F (fun j => (W j).forced) U =
      (Real.exp (R.exponent U) : ℂ) • (Poly.pass (forecast B O F U) * field
        (fun e => bar R.activities B U e + (if crossingBox o A e then
          Mach B (fun j => profile R.activities (W j).forced e U) + O.K e U else 0))
        (flags R.p.threshold U)) := by
  unfold retainedForecast
  congr 3
  funext e
  by_cases h : crossingBox o A e
  · rw [if_pos h, add_assoc]
  rw [if_neg h, add_assoc, crossing_or_zero B R O o W hW hO A U hA e h]

end YM.LocalLTE.Sail.Round2
