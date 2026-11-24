import YM.WilsonMS.Beta.MoonRoll
/-!
# Momentum polynomials for the shifted shell integration

Expand in heat-papers basis in the four-projected coordinates. This gives the
value after applying the actual moment evaluation (shift d not forgotten).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BetaValue.HeatPapers
open Function Filter Set Finset MeasureTheory Metric
open MS Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect Native Horn
open _root_.YM.PertExtension
open RG FormalOPE FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open Complex (I)
open Papers
open scoped Topology ContDiff BigOperators ENNReal
variable {α : ℝ} (h : 0 < α)
set_option quotPrecheck false
local notation "Φ" => Papers.opening mplane (Beam α h)
variable (d x : ℝ)

def paneA : HeatPapers.Poly :=
  (20 : ℝ) • Cubicle d 4 2 0 0 + (40 * x : ℝ) • Cubicle d 3 2 0 0 + (40 : ℝ) • Cubicle d 2 4 0 0 +
                                                      (40 : ℝ) • Cubicle d 2 2 2 0 +
                                                    (40 : ℝ) • Cubicle d 2 2 0 2 +
                                                  (36 * x ^ 2 : ℝ) • Cubicle d 2 2 0 0 +
                                                (16 * x ^ 2 : ℝ) • Cubicle d 2 0 2 0 +
                                              (16 * x ^ 2 : ℝ) • Cubicle d 2 0 0 2 +
                                            (40 * x : ℝ) • Cubicle d 1 4 0 0 +
                                          (40 * x : ℝ) • Cubicle d 1 2 2 0 +
                                        (40 * x : ℝ) • Cubicle d 1 2 0 2 +
                                      (16 * x ^ 3 : ℝ) • Cubicle d 1 2 0 0 +
                                    (16 * x ^ 3 : ℝ) • Cubicle d 1 0 2 0 +
                                  (16 * x ^ 3 : ℝ) • Cubicle d 1 0 0 2 +
                                (20 : ℝ) • Cubicle d 0 6 0 0 +
                              (40 : ℝ) • Cubicle d 0 4 2 0 +
                            (40 : ℝ) • Cubicle d 0 4 0 2 +
                          (28 * x ^ 2 : ℝ) • Cubicle d 0 4 0 0 +
                        (20 : ℝ) • Cubicle d 0 2 4 0 +
                      (40 : ℝ) • Cubicle d 0 2 2 2 +
                    (44 * x ^ 2 : ℝ) • Cubicle d 0 2 2 0 +
                  (20 : ℝ) • Cubicle d 0 2 0 4 +
                (44 * x ^ 2 : ℝ) • Cubicle d 0 2 0 2 +
              (8 * x ^ 4 : ℝ) • Cubicle d 0 2 0 0 +
            (16 * x ^ 2 : ℝ) • Cubicle d 0 0 4 0 +
          (32 * x ^ 2 : ℝ) • Cubicle d 0 0 2 2 +
        (8 * x ^ 4 : ℝ) • Cubicle d 0 0 2 0 +
      (16 * x ^ 2 : ℝ) • Cubicle d 0 0 0 4 +
    (8 * x ^ 4 : ℝ) • Cubicle d 0 0 0 2

lemma paneA_ray (p : QP) : meterR p (paneA d x) = R_A (p 0 - d) (p 1) (p 2) (p 3) x := by
  simp only [paneA, Cubicle, nearer, map_sub, map_pow, map_mul, map_smul, map_add, atP, atR,
    smul_eq_mul, R_A]
  ring

def ValueA (α d x : ℝ) :=
  2 *
      (5 * d ^ 4 * α ^ 2 - 10 * d ^ 3 * α ^ 2 * x + 17 * d ^ 2 * α ^ 2 * x ^ 2 + 40 * d ^ 2 * α -
                12 * d * α ^ 2 * x ^ 3 -
              40 * d * α * x +
            6 * α ^ 2 * x ^ 4 +
          46 * α * x ^ 2 +
        60) /
    α ^ 3

lemma paneA_value : Φ (paneA d x) = ValueA α d x := by
  unfold paneA
  simp only [map_add, map_smul, along_R h]
  norm_num [moment, ValueA]
  field_simp
  ring

def paneS : HeatPapers.Poly :=
  (4 * x : ℝ) • Cubicle d 2 2 0 0 + (4 * x : ℝ) • Cubicle d 2 0 2 0 +
                            (4 * x : ℝ) • Cubicle d 2 0 0 2 +
                          (4 * x ^ 2 : ℝ) • Cubicle d 1 2 0 0 +
                        (4 * x ^ 2 : ℝ) • Cubicle d 1 0 2 0 +
                      (4 * x ^ 2 : ℝ) • Cubicle d 1 0 0 2 +
                    (4 * x : ℝ) • Cubicle d 0 4 0 0 +
                  (8 * x : ℝ) • Cubicle d 0 2 2 0 +
                (8 * x : ℝ) • Cubicle d 0 2 0 2 +
              (2 * x ^ 3 : ℝ) • Cubicle d 0 2 0 0 +
            (4 * x : ℝ) • Cubicle d 0 0 4 0 +
          (8 * x : ℝ) • Cubicle d 0 0 2 2 +
        (2 * x ^ 3 : ℝ) • Cubicle d 0 0 2 0 +
      (4 * x : ℝ) • Cubicle d 0 0 0 4 +
    (2 * x ^ 3 : ℝ) • Cubicle d 0 0 0 2

lemma paneS_ray (p : QP) : meterR p (paneS d x) = R_S (p 0 - d) (p 1) (p 2) (p 3) x := by
  simp only [paneS, Cubicle, nearer, map_sub, map_pow, map_mul, map_smul, map_add, atP, atR,
    smul_eq_mul, R_S]
  ring

def ValueS (α d x : ℝ) :=
  3 * x * (2 * d ^ 2 * α - 2 * d * α * x + α * x ^ 2 + 6) / α ^ 2

lemma paneS_value : Φ (paneS d x) = ValueS α d x := by
  unfold paneS
  simp only [map_add, map_smul, along_R h]
  norm_num [moment, ValueS]
  field_simp
  ring
end YM.WilsonMS.BetaValue.HeatPapers
