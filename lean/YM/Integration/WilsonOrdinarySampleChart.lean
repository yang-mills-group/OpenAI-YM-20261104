import YM.Integration.WilsonOrdinaryDyadicAge
import YM.Integration.WilsonOrdinaryObservedChart

/-! Compare the actual finite chart at every original mesh with the actual field
frame at the canonical sample radius that the matrix march will read. -/
noncomputable section
namespace YM.Integration.WilsonOrdinarySampleChart
open Filter Set Spec Climb OPE RG12 RG17 SharpGram Trace.Pilot
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (J : ℝ → PhysMS.tower S) (P : Pier.Lair.Present F J)
variable {u : Filter (ℕ×ℕ)} (Q : Lenses.Mantle F u) (d : ℕ)

private lemma price {x y b : ℝ} (hx : 0 < x) (hy : 0 < y) (hb : 2 ≤ b)
    (H : x ≤ y*b^4) (n : ℕ) : (2*x/y)^n ≤ b^(5*n) := by
  rw [pow_mul]; apply pow_le_pow_left₀ (by positivity)
  apply (div_le_iff₀ hy).mpr
  calc
    2*x ≤ 2*(y*b^4) := by gcongr
    _ ≤ b*(y*b^4) := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = b^5*y := by ring

include P
/-- An all-level comparison of the two authentic positions, with the same
fixed field space and its two measured frame coordinates on each side. -/
theorem radii (hG : G.Simple) : ∃ p : ℕ, ∀ᶠ k : ℕ in atTop,
    Pier.Lair.Both (C.path.levels.clock.hatBeta k^p) (J (Q.radius k) d)
      (J (Sample.length (Sample.atMesh C k)) d) := by
  obtain ⟨a,T,hT,ranges⟩ := Pier.Lair.ranges F P d
  have via := (tendsto_nhdsWithin_iff.mp WilsonOrdinaryDyadicAge.approaching).1.comp (Sample.sampled_tends C)
  refine ⟨5*a,?_⟩
  filter_upwards [Q.proper,Sample.enough_stops (C:=C) hG 0 0,
      (Next.Rank.Station.hat_rate C.path.levels hG).eventually_ge_atTop 2,
      via.eventually (gt_mem_nhds hT),Q.small.eventually (gt_mem_nhds hT)] with k hr st bnd small little
  let R := Q.radius k; let Z := Sample.length (Sample.atMesh C k); let b := C.path.levels.clock.hatBeta k
  have hR : 0 < R := Q.positive k
  have hZ : 0 < Z := (Sample.samples_spacing _).1
  obtain ⟨W⟩ := st
  have hW : Z ≤ C.S.a k*b^2 ∧ C.S.a k ≤ Z*b^2 := W.match_length
  have hb : 2 ≤ b := bnd
  have p₄ : b^2 ≤ b^4 := pow_le_pow_right₀ (by linarith) (by decide)
  have h₁ : Z ≤ R*b^4 := hW.1.trans (mul_le_mul hr.1 p₄ (by positivity) hR.le)
  have h₂ : R ≤ Z*b^4 := hr.2.trans (by calc
    C.S.a k * b^2 ≤ Z*b^2*b^2 := by gcongr; exact hW.2
    _ = Z*b^4 := by ring)
  by_cases hz : R ≤ Z
  · exact (ranges R Z hR hz small.le).larger (price hZ hR hb h₁ a)
  · exact (ranges Z R hZ (le_of_not_ge hz) little.le).swap.larger (price hR hZ hb h₂ a)

variable (L : Layout F) (hL : Pegs Q L) (E : Services C f S)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field d
include hL E

/-- Pointwise lifts and controls on the *engineering* map used in `ReadingAt`,
all at the original sampled radius, before choosing a linear lift. -/
theorem sample : ∃ p : ℕ, ∀ᶠ k : ℕ in atTop,
    let I := J (Sample.length (Sample.atMesh C k)) d
    (∀ x : D, ∃ v : C.label d, engineering (S:=S) L.charts d k v = I x ∧
      mass C d v ≤ C.path.levels.clock.hatBeta k^p * ‖x‖) ∧
    ∀ v : C.label d, ‖I.symm (engineering (S:=S) L.charts d k v)‖ ≤
      C.path.levels.clock.hatBeta k^p * mass C d v := by
  obtain ⟨m,move⟩ := radii F J P Q d E.simpleGate
  obtain ⟨K,hK,chart⟩ := WilsonOrdinaryObservedChart.original F J P Q L hL E d
  let n := Lenses.price d
  let p := n+m+1
  have growing := Next.Rank.Station.hat_rate C.path.levels E.simpleGate
  refine ⟨p,?_⟩
  filter_upwards [move,chart,growing.eventually_ge_atTop K,growing.eventually_ge_atTop 1] with k hmove hchart hbig hpop
  let a := C.S.a k ^ d; let b := C.path.levels.clock.hatBeta k
  let I := J (Sample.length (Sample.atMesh C k)) d
  let J' := J (Q.radius k) d
  have ha : 0 < a := pow_pos (C.S.a_pos _) _
  have hα : (a:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb : 1 ≤ b := hpop
  have gain : K*b^n*b^m ≤ b^p := by
    calc
      _ ≤ b*b^n*b^m := by gcongr
      _ = _ := by dsimp [p]; rw [pow_succ,pow_add]; ring
  constructor
  · intro x
    obtain ⟨v,hv,price⟩ := hchart.1 ((a:ℂ)⁻¹ • I x)
    have first : ‖J'.symm (I x)‖ ≤ b^m * ‖x‖ := by
      have cal : ‖J'.symm (I x)‖ ≤ b^m * ‖I.symm (I x)‖ := hmove.left (I x)
      simpa only [LinearEquiv.symm_apply_apply] using cal
    refine ⟨v,?_,?_⟩
    · rw [engineering_at,hv,smul_smul]; change ((a:ℂ) * (a:ℂ)⁻¹) • I x = I x
      rw [mul_inv_cancel₀ hα,one_smul]
    · refine price.trans ?_
      rw [map_smul,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg ha.le]
      change K*b^n*a*(a⁻¹*‖J'.symm (I x)‖) ≤ b^p * ‖x‖
      calc
        _ = (K*b^n)*‖J'.symm (I x)‖ := by field_simp
        _ ≤ (K*b^n)*(b^m*‖x‖) := mul_le_mul_of_nonneg_left first (by positivity)
        _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right gain (norm_nonneg _)
  · intro v
    let z := S.project d (L.charts d k v)
    have reverse : ‖I.symm z‖ ≤ b^m * ‖J'.symm z‖ := hmove.right z
    have hh : ‖J'.symm z‖ ≤ K / a * mass C d v := hchart.2 v
    rw [engineering_at,map_smul,norm_smul,Complex.norm_real,Real.norm_of_nonneg ha.le]
    change a*‖I.symm z‖ ≤ b^p * mass C d v
    calc
      _ ≤ a*(b^m*(K/a*mass C d v)) := by
        exact mul_le_mul_of_nonneg_left (reverse.trans (mul_le_mul_of_nonneg_left hh (by positivity))) ha.le
      _ = b^m*K * mass C d v := by field_simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (mass_nonneg ..)
        calc
          _ = K*1*b^m := by ring
          _ ≤ K*b^n*b^m := by gcongr; exact one_le_pow₀ hb
          _ ≤ _ := gain

end YM.Integration.WilsonOrdinarySampleChart
