import YM.Integration.WilsonPhysicalHistoryFieldResite
import YM.Integration.WilsonPhysicalHistoryFieldEnrollment

/-! Individually enroll the genuine translated and rescaled incoming slots
of a finite RG16 block, on the actual family of the existence run. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryBlockInputs
open Filter Function Finset Lattice RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Exterior Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open Pose Glide Bank Dawn Wine Rial Roof Dove Series Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato WilsonRunFormalMarkedStep RG16.Literal RG16.Guarding
open MSbar MSbar.Whisk Push.Uniform
open scoped Classical Topology BigOperators
variable {G : Gauge} {d D : ℕ}

private theorem renamed {V W : Type} (E : V ≃ W) (P : MvPolynomial V ℝ) :
    (MvPolynomial.rename E P).totalDegree=P.totalDegree := MvPolynomial.totalDegree_renameEquiv E P

private theorem sameDegree {n : Side} (x : Site n) (Y : Orb.Pap (wire G n)) (e : ℕ) :
    (PowerSeries.coeff e (WilsonPhysicalHistoryFieldBank.primary n (Kemp.resite x Y))).totalDegree =
      (PowerSeries.coeff e (WilsonPhysicalHistoryFieldBank.primary n Y)).totalDegree := by
  simp only [WilsonPhysicalHistoryFieldBank.primary,PowerSeries.coeff_map]
  change (MvPolynomial.rename _ (PowerSeries.coeff e (Kemp.resite x Y))).totalDegree =
    (MvPolynomial.rename _ (PowerSeries.coeff e Y)).totalDegree
  rw [renamed,renamed]
  simp only [Kemp.resite,PowerSeries.coeff_map]
  exact renamed (Lotus.tint x) _

variable (R : Run G) (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch))
variable (a : hue G) (depth : d<D)

theorem block (i : ℕ) : 2≤(R.family.S.block i).val := by
  have h := R.family.S.block_large i; omega

/-- The actual periodic spatial translation and actual profile passed to
RG16 at the selected finite preimage of the true coarse cell. -/
def incoming (N i : ℕ) (n : Side) (x : Site (R.family.S.block i))
    (w : Letter (R.family.labels.level d)) (f : Studio D) :
    PowerSeries (MvPolynomial (Primary n G) ℝ) :=
  WilsonPhysicalHistoryFieldBank.primary n (Kemp.resite (wrap n (lift x))
    (Kemp.banner d (graph R L a depth N (i+1) w (Dawn.throughW x D (block R i) f)) n))

theorem placed (simple : G.Simple) {u : ℕ→ℕ} (grant : WilsonWindowFormalPurchase.Canonical u R.kit)
    (o : Loc G 1) (s p : ℕ) {δ : ℝ} (δ0 : 0<δ) :
    ∀ᶠ i : ℕ in atTop, ∀ (N : ℕ), i+1≤N → ∀ (w : Letter (R.family.labels.level d))
      (n : Side) (x : Site (R.family.S.block i)) (f : Studio D), ‖f‖≤1 →
      FVA1Physical.Wilson.BankPaid (wrap n (lift x)) (R.family.path.levels.clock.hatBeta (i+1))
        s p (d+p) δ (incoming R L a depth N i n x w f) := by
  obtain ⟨k,fromHere⟩ := eventually_atTop.mp
    (WilsonPhysicalHistoryFieldEnrollment.on_run R L a depth simple grant o s p δ0)
  filter_upwards [eventually_ge_atTop k] with i late
  intro N room w n x f unit
  let V := Dawn.throughW x D (block R i) f
  let Y := Kemp.banner d (graph R L a depth N (i+1) w V) n
  let β := R.family.path.levels.clock.hatBeta (i+1)
  let z := (Lotus.drip n (0,o)).1
  have unit' : ‖Annex.compress D V‖≤1 := (Annex.comp_le V).trans
    ((Dawn.through_le x (block R i) f).trans unit)
  have funded := fromHere (i+1) (late.trans (Nat.le_succ i)) w N room V unit' n
  intro e he
  let t := wrap n (lift x)
  have h0 : z=0 := by simp [z,Lotus.drip]
  have h1 := WilsonPhysicalHistoryFieldResite.funded (Mosaic.αm β) s (d+p) z t Y e (β^δ)
    ((funded.1 e he).2)
  have h2 := (sameDegree t Y e).le.trans (funded.1 e he).1
  refine ⟨h2,?_⟩
  change Whisk.Vault (Measuring.chart n G) {t} (Mosaic.αm β) s (d+p) 0
    (PowerSeries.coeff e (WilsonPhysicalHistoryFieldBank.primary n (Kemp.resite t Y))) (β^δ)
  rw [h0,zero_add] at h1
  exact h1

end YM.Integration.WilsonPhysicalHistoryBlockInputs

