import YM.Integration.WilsonPhysicalHistoryFieldSpread

/-! Charge the true physical zero-background angular seminorm to the
original independent formal insertion on the same ultraviolet history. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryFieldVault
open Function Filter Finset Lattice Laurent RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Exterior Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open Pose Glide Bank Dawn Wine Rial Roof Dove Series Trellis Aster Borough Elm Dove.Lab
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato WilsonRunFormalMarkedStep RG16.Literal RG16.Guarding
open RG16 RG16.Literal RG16.Guarding Pert.Asymptotics Trace.Physical Next.Foundations
open MSbar MSbar.Whisk Push.Uniform FVA1Physical.Round2.Curvature
open WilsonPhysicalHistoryFieldDerivatives WilsonPhysicalHistoryFieldSpread
open WilsonPhysicalHistoryAperture WilsonPhysicalHistoryFieldTail
open scoped Classical Topology BigOperators ENNReal
variable {G : Gauge} {n : Side} {r d D : ℕ}

private theorem bill (z : wire G n) (b C : ℝ) (T : Tile (wire G n) r)
    (h : Knoxville (lake n _) b z T C) :
    ∑ v : Fin r→wire G n, Real.exp (b*Gorge.wide (lake n _) (Fin.cons z v))*‖T v‖ ≤ C := by
  apply (ENNReal.ofReal_le_ofReal_iff h.1).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun v _=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
  have rent := h.2
  rw [tsum_fintype] at rent
  simpa only [Gorge.shine, ← ofReal_norm, ← ENNReal.ofReal_mul (Real.exp_pos _).le] using rent

private theorem point (z : wire G n) {b α : ℝ} (hb : 0<b) (hα : α≤b/2) (s : ℕ)
    (P : MvPolynomial (wire G n) ℝ) (v : Fin r → Primary n G) :
    Whisk.rate (Measuring.chart n G) {z.1} α s 0
      (MvPolynomial.rename (coordinates G n).symm P) (List.ofFn v) ≤
      ((r.factorial:ℝ)*WilsonPhysicalHistoryFieldSpread.fee b s)*
      (Real.exp (b*Gorge.wide (lake n _) (Fin.cons z (coordinates G n ∘ v)))*
        ‖marble r P (coordinates G n ∘ v)‖) := by
  unfold Whisk.rate
  rw [WilsonPhysicalHistoryFieldDerivatives.kernel (coordinates G n) r P v,
    abs_mul, abs_of_nonneg (Nat.cast_nonneg r.factorial),Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_right (WilsonPhysicalHistoryFieldSpread.spread hb hα s z v)
    (mul_nonneg (Nat.cast_nonneg r.factorial)
      (abs_nonneg (marble r P (coordinates G n ∘ v))))).trans_eq
  ring

private theorem exchange {V W : Type} [Fintype V] [Fintype W] (E : V ≃ W)
    (F : (Fin r → W)→ℝ) :
    (∑ v : Fin r→V, F (E ∘ v)) = ∑ q : Fin r→W, F q :=
  (Equiv.piCongrRight fun _ : Fin r=>E).sum_comp F

/-- Each actual ordered physical seminorm is controlled by the very same
symmetric kernel, on the original finite period and with its true anchor. -/
theorem order (z : wire G n) {b α C : ℝ} (hb : 0<b) (hα : α≤b/2) (s : ℕ)
    (P : MvPolynomial (wire G n) ℝ) (h : Knoxville (lake n _) b z (marble r P) C) :
    Whisk.lump (Measuring.chart n G) {z.1} α s r 0
      (MvPolynomial.rename (coordinates G n).symm P) ≤
      ((r.factorial : ℝ)*WilsonPhysicalHistoryFieldSpread.fee b s)*C := by
  classical
  let E := coordinates G n
  let F (v : Fin r → wire G n) :=
    Real.exp (b*Gorge.wide (lake n _) (Fin.cons z v))*‖marble r P v‖
  let A := (r.factorial : ℝ)*WilsonPhysicalHistoryFieldSpread.fee b s
  have A0 : 0≤A := mul_nonneg (Nat.cast_nonneg _) (fee_nonneg hb s)
  unfold Whisk.lump
  rw [word_function_sum]
  calc
    _ ≤ ∑ v : Fin r → Primary n G, A * F (E ∘ v) := by
      apply Finset.sum_le_sum
      intro v _
      exact point z hb hα s P v
    _ = A * ∑ q : Fin r→wire G n, F q := by rw [←Finset.mul_sum,exchange E F]
    _ ≤ _ := mul_le_mul_of_nonneg_left (bill z b C (marble r P) h) A0

variable (R : Run G) (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch))
variable (a : hue G) (depth : d<D)

/-- The genuine, *untruncated* anchored seminorm from the independent original
`Elm.terrace` on this run, including all finite observing periods. -/
theorem all_fields (simple : G.Simple) {u : ℕ→ℕ} (grant : WilsonWindowFormalPurchase.Canonical u R.kit)
    (o : Loc G 1) (E : ℕ) (w : Letter (R.family.labels.level d)) (r : ℕ) :
    ∃ (B : ℝ) (m : ℕ), 0≤B ∧
    ∀ᶠ i : ℕ in atTop, ∀ (N : ℕ), i≤N → ∀ (f : Studio D) (e : ℕ), e≤E → ∀ n : Side,
      Knoxville (lake n _) (width R.family i) (Lotus.drip n (0,o))
        (rancho (Kemp.banner d (graph R L a depth N i w f) n) e r)
        (B*(Borough.ageZ (R.family.path.levels.clock.hatBeta i))^m *‖Annex.compress D f‖) := by
  let C := R.family
  let J := d+D+E+5
  have j5 : 5≤J := by dsimp [J];omega
  have jD : D≤J := by dsimp [J];omega
  have jE : E≤J := by dsimp [J];omega
  have jd : d+3≤J := by dsimp [J];omega
  obtain ⟨K,after⟩ := eventually_atTop.mp (C.path.levels.fits.deep.eventually_ge_atTop J)
  have gate : J≤C.path.levels.clock.J (K+1) := after _ (Nat.le_succ K)
  let ann := WilsonWindowFormalAnnouncement.on_run R grant
  obtain ⟨B,m,B0,archive⟩ := Primer.landedFields C simple a L o ann j5 gate jE depth jd jD w r
  refine ⟨B,m,B0,?_⟩
  filter_upwards [eventually_ge_atTop K] with i past
  intro N cap f e he n
  let Z := graph R L a depth N i w f e r
  have funded : Knoxville (fame _) (width C i) (0,o) Z
      (B*(Borough.ageZ (C.path.levels.clock.hatBeta i))^m*‖Annex.compress D f‖) := by
    dsimp only [Z]
    rw [WilsonPhysicalHistoryFieldTail.prescribed R L a depth grant]
    exact ((archive i past f e he).2.2 N cap).1
  have trained : d≤C.path.levels.clock.J (i+1) :=
    (by omega : d≤J).trans (after _ (past.trans (Nat.le_succ _)))
  have integrity := Sierra.ritual_cell o f ((normalized R L a depth simple o N i cap trained).officers w)
  rw [Kemp.badge _ integrity.young integrity.committees (slotsFits (C.labels.level d) w) n e r]
  exact sieve_bill n Z _ (width_pos C i).le funded

end YM.Integration.WilsonPhysicalHistoryFieldVault

