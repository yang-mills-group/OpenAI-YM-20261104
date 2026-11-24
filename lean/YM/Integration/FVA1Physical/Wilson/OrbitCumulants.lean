import YM.Integration.FVA1Physical.Wilson.OrbitSources

/-! Mixed moments and connected logarithms at finite marker load, with the
explicit positive support weights in the marker norm. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function MeasureTheory Finset Lattice RG YM.Wilson Tree Marker RGComparison.Core16
open MSbar MSbar.Heath MSbar.Heath.Cottage MSbar.Bulk Comparison.RG02.Order Extra.Trajectories
open scoped Classical
variable {G : Gauge} {f c : Side} {S : StepData c f} {Y : Support f}
variable {I : Type} [DecidableEq I] (C : Census I) (F : I → Config G f→ℂ)

lemma orbit_table_cap (w : I→ℝ) (hw : ∀ i,0<w i) (P : (Config G f→ℝ)→ℝ)
    (hF : ∀ i,LocalInsertion S Y (F i)) {b : ℝ}
    (cap : ∀ φ, GaugeLocal S Y φ → (∀ U,|φ U|≤1) → |P φ|≤b) :
    Poly.price w (orbitMoments C F P) ≤ (∑ s:C.Mode,Poly.toll w s)*(2*b) := by
  rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro s _
  have h := LocalInsertion.products hF s.val
  have a := cap _ h.real.1 h.real.2
  have b' := cap _ h.imag.1 h.imag.2
  apply mul_le_mul_of_nonneg_left _ (Poly.worth hw s).le
  exact (Complex.norm_le_abs_re_add_abs_im _).trans ((add_le_add a b').trans_eq (two_mul b).symm)

/-- The logarithmic cost is bounded using only the prescribed finite marker
horizon and weights. It is independent of the density, volume and forest orbit. -/
theorem orbit_connected_price [Fintype I] (w : I→ℝ) (hw : ∀ i,0<w i)
    (E W : (Config G f→ℝ)→ℝ) (hF : ∀ i, LocalInsertion S Y (F i)) {ε : ℝ} (small : ε≤1)
    (unitE : E 1=1) (zeroE : E 0=0) (unitW : W 1=1) (zeroW : W 0=0)
    (normE : ∀ φ, GaugeLocal S Y φ → (∀ U,|φ U|≤1) → |E φ|≤1)
    (bill : ∀ φ, GaugeLocal S Y φ → (∀ U,|φ U|≤1) → |W φ-E φ|≤ε) :
    let t := ∑ s:C.Mode,Poly.toll w s
    Poly.price w (connected (orbitMoments C F W)-connected (orbitMoments C F E)) ≤
      repeats (Fintype.card I) (1+t*4) * (t*(2*ε)) := by
  intro t
  let P:=orbitMoments C F W
  let Q:=orbitMoments C F E
  have t₀ : 0≤t := sum_nonneg fun i _=>(Poly.worth hw i).le
  have cap (φ : Config G f→ℝ) (hh : GaugeLocal S Y φ) (hb : ∀ U,|φ U|≤1) : |W φ| ≤ 2 := by
    calc |W φ|=|(W φ-E φ)+E φ| := by rw [sub_add_cancel]
         _ ≤ |W φ-E φ|+|E φ| := abs_add_le ..
         _ ≤ _ := by linarith only [small,bill φ hh hb,normE φ hh hb]
  have cP := orbit_table_cap C F w hw W hF cap
  have cQ := orbit_table_cap C F w hw E hF normE
  have hP : Poly.price w (1-P) ≤ 1+t*4 := by
    refine (priced_sub w hw _ _).trans ?_
    rw [Poly.one_price]; rw [show (2:ℝ)*2=4 by norm_num] at cP; exact add_le_add le_rfl cP
  have hQ : Poly.price w (1-Q) ≤ 1+t*4 := by
    refine (priced_sub w hw _ _).trans ?_
    rw [Poly.one_price]; apply add_le_add le_rfl
    exact cQ.trans (mul_le_mul_of_nonneg_left (by norm_num) t₀)
  have H := lip P Q w hw (orbitMoments_quiet C F W unitW zeroW)
    (orbitMoments_quiet C F E unitE zeroE) hP hQ (Fintype.card I) (fun t=>card_le_univ t.val)
  exact H.trans (mul_le_mul_of_nonneg_left (orbit_mixed_price C F w hw E W hF bill)
    (repeats_pos _ _ (by positivity)))
end YM.Integration.FVA1Physical.Wilson
