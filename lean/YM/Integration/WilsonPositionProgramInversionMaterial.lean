import YM.Integration.WilsonPositionProgramInversionRank
import YM.Integration.WilsonPositionProgramMasterBirth

/-! The same normalized inversion tree receives the full series of an original
submitted source. Reannounced field coefficients multiply before extraction,
with one exact vacuum denominator for every proper or complete ordinary word. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true

namespace YM.Integration.WilsonPositionProgramInversionMaterial
open Finset Lattice Wilson RG XSpace RegulatorIR.FVAAlt2 PertExtension PertExtension.Orb
open PhysicalNext.Repeat.Legato Precision Labels
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Soil WilsonCoeffUV.Shard
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (p : XSpace.Period) {I : Type} [Fintype I] [LinearOrder I]
    (d : I → ℕ) (z : I → Cover)
local notation "F" j => R.family.labels.level (d j)
abbrev Axes := (j : I) → Alma (F j)
def axis (a : Axes R d) := fun j => sheet (F j) (a j)
def degree (a : Axes R d) := Kick.depthF univ d (axis R d a)
def ceiling := ∑ j, WilsonPositionProgramMasterBirth.rank R (d:=d j)
def dose (v : (j : I) → Verse (F j)) (h : I → ℕ) (fit : ∀ j, d j < h j)
    (b : (j : I) → Volume (h j)) (a : Axes R d) : PowerSeries ℂ :=
  ∏ j, PowerSeries.map (algebraMap ℝ ℂ) (v j (a j)) *
    PowerSeries.C ((jewelBloom (fit j) (a j) (b j) : ℝ) : ℂ)

variable (T : p.Tree)
def source (a : Axes R d) : XSpace.Bare.Series T G :=
  XSpace.Taylor.expandTaylor (T.basis G) (Complex.ofRealCLM ∘
    (WilsonPositionProgramCopyTop.planted R p d z (axis R d a) ∘ T.links))

def finite (ζ : Axes R d → PowerSeries ℂ) : XSpace.Bare.Series T G :=
  ∑ a, XSpace.Bare.scalar T (PowerSeries.X^(ceiling R d-degree R d a) * ζ a) *
    source R p d z T a

def reported (D : ChartRatio G) (a : Axes R d) : PowerSeries ℂ :=
  PowerSeries.mk fun q => ((YM.FVAAlt2.Fixed.treeMom D
    (WilsonPositionProgramCopyTop.planted R p d z (axis R d a)) (degree R d a) q : ℝ) : ℂ)

omit [LinearOrder I] in
theorem rank_le (a : Axes R d) : degree R d a ≤ ceiling R d :=
  Finset.sum_le_sum fun j _ => Finset.le_sup (f:=valence (F j)) (mem_univ (a j))

theorem one (D : ChartRatio G) (law : LocalRatio D) (a : Axes R d) :
    XSpace.Bare.normalized T G (source R p d z T a) =
      PowerSeries.X^(degree R d a) * reported R p d z D a := by
  apply PowerSeries.ext
  intro k
  rw [PowerSeries.coeff_X_pow_mul']
  split
  · rename_i hk
    rw [reported,PowerSeries.coeff_mk]
    have h := WilsonPositionProgramCopyTop.original R p d z (axis R d a) D law T (k-degree R d a)
    change PowerSeries.coeff k (WilsonPositionProgramCopyTop.normalized R p d z (axis R d a) T) = _
    change PowerSeries.coeff (k-degree R d a+degree R d a)
      (WilsonPositionProgramCopyTop.normalized R p d z (axis R d a) T) = _ at h
    rwa [Nat.sub_add_cancel hk] at h
  · exact WilsonPositionProgramInversionRank.original R p d z (axis R d a) T k (by change k < degree R d a; omega)

theorem original (D : ChartRatio G) (law : LocalRatio D) (ζ : Axes R d → PowerSeries ℂ) :
    XSpace.Bare.normalized T G (finite R p d z T ζ) =
      PowerSeries.X^(ceiling R d) * ∑ a, ζ a * reported R p d z D a := by
  rw [finite,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [XSpace.Bare.normalized_scalar,one R p d z T D law]
  rw [show ceiling R d=ceiling R d-degree R d a+degree R d a from
    (Nat.sub_add_cancel (rank_le R d a)).symm,pow_add]
  simp only [Nat.add_sub_cancel]
  ring

end YM.Integration.WilsonPositionProgramInversionMaterial
end
