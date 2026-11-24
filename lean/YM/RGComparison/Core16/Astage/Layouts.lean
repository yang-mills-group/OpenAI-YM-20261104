import YM.RGComparison.Core16.Astage.Wings
/-!
# Deploy precision/telescope bridges

Feed the actual smooth compact ψ reports (or any producer at available test norm/degree and
apertures/center offsets). `Wing` & `measured` allow dependence on smooth-profile parameters by
comap product filter; include derivative demand EXPONENT in that profile norm, *uniform* with
no growth in internal perturbative orders. The adapters here are for the specified power-of-log
geometry, not a special fixed separation or a near-diagonal extension. `μ` & `p` in all these
readers are in **reported/r scaled center-test units**, positive gap. Continue to use construction
supports & masks before grouping, not move them as functions of these external read-side profiles.
Final estimates have form `Xi` here. Require fixed setup behind B,b, etc., not reporting ratio
or inverse defined using current physical Gram. See Companion table.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Astage.Layouts
open Function Filter Real Metric Set MeasureTheory OPE Labels Table Orbits Axle Tape
open Ward Extraction Spec Panel
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {C:Family G}{S:Table C.book}{ι:Type}{φ:Filter ι}
local notation "a"=> C.S.a
variable (h:G.Simple){m:ι→ℕ}(hm:Tendsto m φ atTop)
local notation "s₀"=> ruler C m
local notation "Λ"=> budgetLog C m
include hm h
lemma room {β:ℝ}(_hb:20<β){r:ι→ℝ}
    (hp:∀ᶠ i in φ,(C.S.a (m i))*(Λ i)^β ≤ r i ∧ r i ≤ (C.S.a (m i))*(Λ i)^(β+1)) : RateIs φ s₀ r (-1:ℝ):=by
    have ht:= large_s C hm; have hf:= large_Λ C h hm; let b:= β+1; have ha:= (ruler_height (C:=C) hm).mesh;
    have hy: RateIs φ s₀ Λ 0:= RateIs.of_sandwich (RateIs.const ht one_pos) (Panel.cheap hm h) (hf.eventually_ge_atTop 1) (Eventually.of_forall fun _=> le_rfl) ht
    exact RateIs.of_sandwich ( (ha.mul (hy.rpow β)).swap (by ring)) (((ha.mul (hy.rpow (β+1))).swap (by ring)).pays ht) (hp.mono fun i hi=>hi.1) (hp.mono fun i hi=>hi.2) ht

omit h
variable {I:Type}[Fintype I]
lemma shape {r:ι→ℝ}{x:ι→ I→ E4}{o:ι→E4}{d δ:ℝ}(hd:0 ≤ d)(he:0<δ)(hr:RateIs φ s₀ r (-1))
    (hz: ∀ᶠ i in φ, WithinRoom (r i) d δ (x i) (o i)): enveloped φ s₀ 1 x o ∧ Kept φ s₀ 1 x:=by
    have ht:=large_s C hm
    constructor
    · apply (((RateLE.const d ht).mul (hr.pays ht)).mono (by simp)).of_norm_le
      filter_upwards [hr.pos,hz] with i hi hb using (pi_norm_le_iff_of_nonneg (mul_nonneg hd hi.le)).mpr hb.span
    · intro b hb; filter_upwards [hz,((RateIs.const ht he|>.mul hr).swap (zero_add _)|>.overtakes (RateLE.exp (-b) ht) ht (by linarith))] with i hi hb using fun j k jk=>hb.trans_le (hi.spaced j k jk)

omit hm
-- parameter B can encode physics labels and tunes at fixed setup. Don't choose constants after
-- b placement with b moving. Choose using Filter and an arbitrary announced Domain. `Ξ` is the
-- needed test-norm loss with growth; this scaling lemma costs **same** norm; never changes Ψ-test.
def all {α:Type*} (m:α→ℕ):Filter α:= Filter.comap m atTop
lemma portable {α:Type*} (m:α→ℕ): Tendsto m (all m) atTop:= tendsto_comap
lemma read_all {α:Type*} (m:α→ℕ){p:α→Prop}: (∀ᶠ i in all m,p i) ↔ ∃ n,∀ z:α,n ≤ m z → p z:=by
   rw [all,eventually_comap,eventually_atTop]; constructor
   · rintro ⟨n,hn⟩; exact ⟨n,fun z hz=> hn _ hz z rfl⟩
   rintro ⟨n,hN⟩; exact ⟨n,fun i hi z hz=>hN z (hz.symm ▸ hi)⟩

set_option quotPrecheck false
variable {g:ι→ℝ}{H X:Type}[SMul ℝ H][NormedAddCommGroup X][NormedSpace ℂ X]
/-- Restore the unnormalized estimates after proving them on unit profiles in the prescribed
homogeneous profile norm. Use at *any test order* k from the Ledger where the norms qualify,
only pay once. Statement allows keeping domain of support in H, defining its norm separately
(scaling & price are explicit hypotheses). -/
lemma restore (P:ι→H→X)(r q:ℕ)(N:H→ℝ)(hN:∀ x,0≤ N x)
   (p:∀ x,∃ y, N y ≤1 ∧ N x • y=x)(hP:∀ i x (z:ℝ), P i (z • x)=(z:ℂ) • P i x)
   (hu : ∀ᶠ i in φ, ∀ x,N x ≤1 → ‖P i x‖ ≤ g i^(r+1)* Λ i^q): ∀ᶠ i in φ,∀ x, ‖P i x‖ ≤ g i^(r+1)*Λ i^q * N x:=by
    filter_upwards [hu] with i hi x
    obtain ⟨y,hy,he⟩:=p x
    calc _ = ‖(N x:ℂ) • P i y‖:=by rw [← hP i y (N x),he]
         _ ≤ _:=by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (hN x), mul_comm]; exact mul_le_mul_of_nonneg_right (hi y hy) (hN x)
end YM.RGComparison.Core16.Astage.Layouts
