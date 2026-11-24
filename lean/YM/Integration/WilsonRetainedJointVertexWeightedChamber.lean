import YM.Integration.WilsonRetainedJointVertexChamber
import YM.Integration.WilsonRetainedJointVertexMarked

/-! The signed multi-vertex Taylor error with a Gaussian-integrable marked cofactor. -/
noncomputable section
set_option autoImplicit false

namespace YM.Integration.OriginalMarkedRunAction
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato
open Dict06.Series RGLocalTaylor.Insert
open Work.F03 Bid Coat Matter
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open scoped Topology BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {R : Rep G f}
variable {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ} {o : Target.Order G W}

/-- The product uses a single forest, held slice and Gaussian. Slots may coincide.
The signed spectator spends one additional Hölder slot. -/
theorem chamber_marked (H : Cash W s μ L Q o C T R) (temp : 0 ≤ Pressure.temp s)
    (χ : Chi) (v : Finset (LocalLTE.Fan.Veil c f)) (i : Greenbelt.Reserve S) (tag : S.Choices)
    (y : (Greenbelt.allot i).Slice G) (Z : SeriesA G) (n K : ℕ)
    (σ D : Fin (n+1) → ℝ) (hs : ∀ j, 0 < σ j) (filed : ∀ j, Draw Z (σ j) (D j))
    (a : Fin (n+1) → PrismA G) (member : ∀ j, a j ∈ Z) (x : Fin (n+1) → Site f)
    (g p : ℝ) (hg : 0 < g) (small : g ≤ 1) (lo : 1/2 ≤ p) (hi : p ≤ 3/2)
    (J : Air f G → ℂ) {B : ℝ} (hB : 0 ≤ B) :
    let F := Greenbelt.allot i
    let X := WilsonCoherentMayerHearing.chamber T s o.K χ 1 v i tag
    let β := Integral.temperature g
    let w := fun j => β*p*(g/Real.sqrt p)^((a j).grade-(a j).rise)
    let physical := fun (j : Fin (n+1)) (z : Air f G) =>
      (w j : ℂ) * sitePacket (a j).cells (x j) ((X.wrapY y).input ((X.wrapY y).liftA β z))
    let polynomial := fun (j : Fin (n+1)) (z : Air f G) =>
      (w j : ℂ) * siteTaylor (a j).cells (x j) (angularSample F z) ((a j).rise+K+1) g
    let cost := fun j r => occurrencePrice G L o.eta o.gap o.ample (σ j) (D j) (a j) r (n+2)
    let error := fun z => J z * ((∏ j, polynomial j z) - ∏ j, physical j z)
    AEStronglyMeasurable J X.dice →
    (Integrable (fun z => ‖J z‖^(n+2)) X.dice ∧ ∫ z, ‖J z‖^(n+2) ∂X.dice ≤ B^(n+2)) →
      Integrable error X.dice ∧
        ‖∫ z, error z ∂X.dice‖ ≤
          B * ((2 : ℝ)^(n+2) * g^(K + ∑ j, (a j).grade) *
            ∏ j, max (cost j (a j).rise) (cost j ((a j).rise+K))) := by
  intro F X β w physical polynomial cost error jm paid
  let amount (j : Fin (n+1)) := cost j (a j).rise * g^(a j).grade
  let missed (j : Fin (n+1)) := cost j ((a j).rise+K) * g^((a j).grade+K)
  let united (j : Fin (n+1)) := max (cost j (a j).rise) (cost j ((a j).rise+K))
  have pos (j : Fin (n+1)) (r : ℕ) : 0 ≤ cost j r := by
    dsimp only [cost, occurrencePrice]
    have d := (filed j).1
    have h := (speed_price_pos G L o.eta o.gap o.ample ((r+2)*(n+2)-1)).le
    exact mul_nonneg (mul_nonneg (by positivity) d)
      (pow_nonneg (div_nonneg (mul_nonneg (by norm_num) h) (hs j).le) _)
  have am (j : Fin (n+1)) : AEStronglyMeasurable (physical j) X.dice := by
    have got := chamber_grade H temp χ v i tag y Z (hs j) (filed j) (a j)
      (member j) (x j) g p hg lo hi (fun _ => (1 : ℂ)) (B := 1)
      (fun _ => by simp) aestronglyMeasurable_const
    simpa only [physical, w, β, X, one_mul] using got.1.1
  have tm (j : Fin (n+1)) : AEStronglyMeasurable (polynomial j) X.dice := by
    have got := chamber_vertex H temp χ v i tag y Z (hs j) (filed j) (a j)
      (member j) (x j) ((a j).rise+K+1) g p hg (fun _ => (1 : ℂ)) (B := 1)
      (fun _ => by simp) aestronglyMeasurable_const
    have dm : AEStronglyMeasurable (fun z => physical j z - polynomial j z) X.dice := by
      simpa only [physical, polynomial, w, β, F, X, one_mul, mul_sub] using got.1.1
    have full := (am j).sub dm
    simpa only [Pi.sub_def, sub_sub_cancel] using full
  have actual (j : Fin (n+1)) :
      Integrable (fun z => ‖physical j z‖ ^ (Fintype.card (Fin (n+1))+1)) X.dice ∧
      ∫ z, ‖physical j z‖ ^ (Fintype.card (Fin (n+1))+1) ∂X.dice ≤
        amount j ^ (Fintype.card (Fin (n+1))+1) := by
    simpa only [Fintype.card_fin, physical, w, β, X, amount, cost, occurrencePrice]
      using chamber_grade_moment H temp χ v i tag y Z (hs j) (filed j) (a j) (member j) (x j) (n+1) g p hg lo hi
  have change (j : Fin (n+1)) :
      Integrable (fun z => ‖polynomial j z-physical j z‖ ^ (Fintype.card (Fin (n+1))+1)) X.dice ∧
      ∫ z, ‖polynomial j z-physical j z‖ ^ (Fintype.card (Fin (n+1))+1) ∂X.dice ≤
        missed j ^ (Fintype.card (Fin (n+1))+1) := by
    have align : (a j).grade-(a j).rise+((a j).rise+K)=(a j).grade+K := by
      have rank := (a j).rankA
      omega
    have got := chamber_power_moment H temp χ v i tag y Z (hs j) (filed j)
      (a j) (member j) (x j) ((a j).rise+K) (n+1) g p hg lo hi
    simp only [Fintype.card_fin, polynomial, physical, missed, cost, occurrencePrice,
      ← mul_sub, norm_mul, norm_sub_rev (siteTaylor _ _ _ _ _) _]
    simpa only [norm_mul, F, X, β, w, align] using got
  have ac (j) : 0 ≤ amount j := mul_nonneg (pos j _) (pow_nonneg hg.le _)
  have ex (j) : 0 ≤ missed j := mul_nonneg (pos j _) (pow_nonneg hg.le _)
  have base (j) : amount j ≤ united j * g^(a j).grade :=
    mul_le_mul_of_nonneg_right (le_max_left ..) (pow_nonneg hg.le _)
  have more (j) : missed j ≤ g^K * (united j * g^(a j).grade) := by
    dsimp only [missed]
    rw [pow_add, mul_comm (g^K), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg hg.le _)) (pow_nonneg hg.le _)
  obtain ⟨int, bill⟩ := joined_marked_price X.dice physical polynomial amount missed
    (fun j => united j*g^(a j).grade) am tm ac ex actual change
    (pow_nonneg hg.le K) (pow_le_one₀ hg.le small) base more J jm hB
    (by simpa only [Fintype.card_fin] using paid)
  refine ⟨int, ?_⟩
  calc
    _ ≤ B*((2:ℝ)^(Fintype.card (Fin (n+1))+1)*g^K*∏ j, (united j*g^(a j).grade)) := bill
    _ = _ := by
      rw [Fintype.card_fin, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, pow_add]
      ring

end YM.Integration.OriginalMarkedRunAction

