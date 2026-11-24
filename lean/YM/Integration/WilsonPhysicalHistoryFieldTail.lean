import YM.Integration.WilsonPhysicalHistoryAperture
import YM.FormalBulk08.Primer.Fields

/-! Spatial tail in the genuinely filed finite independent marked fields:
physical aperture choice and arbitrary coupling order, on the single
funded existence trajectory, including the actual observing tori. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryFieldTail

open Filter Real Lattice RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Exterior Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open Pose Glide Bank Dawn Wine Rial Roof Dove Series Trellis Aster Borough Elm Dove.Lab
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato WilsonRunFormalMarkedStep WilsonPhysicalHistoryAperture
open RG16 RG16.Literal RG16.Guarding Pert.Asymptotics Trace.Physical Next.Foundations
open scoped Classical Topology ENNReal BigOperators

variable {G : Gauge} (R : Run G) {d D : ℕ}
variable (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch)) (a : hue G) (depth : d<D)

theorem prescribed {u : ℕ→ℕ} (grant : WilsonWindowFormalPurchase.Canonical u R.kit) (N i : ℕ) :
    graph R L a depth N i=Primer.fieldCoeffs R.family a L depth N i := by
  let line (ρ : ChartRatio G) := Elm.terrace ρ R.family.path.levels L (Hay.Wday _) a
    (R.family.labels.level d) (R.family.localSection d) depth N i
  exact congrArg line grant.1

/-- Cover, every finite observing torus, and signed cutoff-minus-limit:
the true tested kernel mass past the stated aperture is paid by any
prescribed positive power of the real regulated local coupling. -/
theorem measured (simple : G.Simple) {u : ℕ→ℕ} (grant : WilsonWindowFormalPurchase.Canonical u R.kit)
    (o : Loc G 1) (E p : ℕ) (w : Letter (R.family.labels.level d)) (r : ℕ) :
    ∀ᶠ i : ℕ in atTop, ∀ (N per : ℕ), i≤N → ∀ (f : Studio D) (e : ℕ), e≤E →
      let Z := graph R L a depth N i w f e r
      let Y := Primer.fieldLimit R.family a L depth i w f e r
      let A := radius R.family p i
      let g := regulatorRun R.family N per i
      let b := g^p*‖Annex.compress D f‖
      let h := g^p*ratioR R.family.S N i targetPower*‖Annex.compress D f‖
      mass (fame _) (0,o) A Z ≤ ENNReal.ofReal b ∧
      mass (fame _) (0,o) A (Z-Y) ≤ ENNReal.ofReal h ∧
      ∀ n : Side,
        mass (lake n _) (Lotus.drip n (0,o)) A (rancho (Kemp.banner d (graph R L a depth N i w f) n) e r) ≤ ENNReal.ofReal b ∧
        mass (lake n _) (Lotus.drip n (0,o)) A (sieve n (Z-Y)) ≤ ENNReal.ofReal h := by
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
  filter_upwards [eventually_ge_atTop K,WilsonPhysicalHistoryFormalPayoff.polynomial R simple B B0 m
    (show (0:ℝ)<1 by norm_num)] with i past revenue N per cap f e he
  intro Z Y A g b h
  let β := C.path.levels.clock.hatBeta i
  let age := Borough.ageZ β
  let η := width C i
  let P := ‖Annex.compress D f‖
  let s := B*age^m
  let T := ratioR C.S N i targetPower
  have width0 := (width_pos C i).le
  have G0 : 0<g := g_pos R.makes cap
  have age0 : 0≤age := zero_le_one.trans (Borough.progZ (ann.power.beta i))
  have earn : s≤g^(-(1:ℝ)) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ age0 (WilsonPhysicalHistoryAperture.age C i) m) B0).trans
      (revenue N per cap)
  have fund : Real.exp (-η*(A:ℝ))*s ≤ g^p := by
    have localPrice := exponential R p N per i cap
    calc
      _ ≤ g^(p+1)*g^(-(1:ℝ)) := mul_le_mul localPrice earn (mul_nonneg B0 (pow_nonneg age0 _)) (pow_nonneg G0.le _)
      _ = _ := by rw [Real.rpow_neg_one,pow_succ,mul_assoc,mul_inv_cancel₀ G0.ne',mul_one]
  have bound := (archive i past f e he).2.2 N cap
  have normZ : Knoxville (fame _) η (0,o) Z (s*P) := by
    unfold Z
    rw [prescribed R L a depth grant]
    exact bound.1
  have normD : Knoxville (fame _) η (0,o) (Z-Y) (s*T*P) := by
    unfold Z
    rw [prescribed R L a depth grant]
    exact bound.2
  have P0 : 0≤P := norm_nonneg _
  have T0 : 0≤T := (ratioR_pos ..).le
  have low : ENNReal.ofReal (Real.exp (-η*(A:ℝ))*(s*P)) ≤ ENNReal.ofReal b :=
    ENNReal.ofReal_le_ofReal (by change _ ≤g^p*P; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right fund P0)
  have lower : ENNReal.ofReal (Real.exp (-η*(A:ℝ))*(s*T*P)) ≤ ENNReal.ofReal h :=
    ENNReal.ofReal_le_ofReal (by change _ ≤g^p*T*P; rw [←mul_assoc,←mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right fund T0) P0)
  refine ⟨(tail normZ width0 A).trans low,(tail normD width0 A).trans lower,?_⟩
  intro n
  have trained : d≤C.path.levels.clock.J (i+1) := (by omega : d≤J).trans (after _ (past.trans (Nat.le_succ _)))
  have integrity := Sierra.ritual_cell o f ((normalized R L a depth simple o N i cap trained).officers w)
  rw [Kemp.badge _ integrity.young integrity.committees (slotsFits (C.labels.level d) w) n e r]
  exact ⟨(tail (sieve_bill n Z _ width0 normZ) width0 A).trans low,
    (tail (sieve_bill n (Z-Y) _ width0 normD) width0 A).trans lower⟩

end YM.Integration.WilsonPhysicalHistoryFieldTail

