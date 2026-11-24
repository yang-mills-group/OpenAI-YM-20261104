import YM.Integration.WilsonPhysicalOrientedStencilPin

/-! The actual commissioned station bounds the reflected, fully restored
finite input and its complete finite stencil sum before any Taylor order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalOrientedPivotSalary
open Function Filter Finset Lattice Wilson RG Labels Source Pert.Asymptotics Extra.Histories
open WilsonPhysicalOrientedStencilPin (dosesAt)
open WilsonReceivedCanonicalVersePortfolio (Selection weight wallet)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkMixedSeed (units doses)
open PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){n N per K f requested power age:ℕ}{B:ℝ}(d:Fin n→ℕ)
  (file:Filed R d K){fk:f≤K}{kn:K≤N}(A:Panel R d N per f K fk kn requested power age B)
  (station:A.slot=file.station)(axes:A.axis=file.A N per)
local notation "heat" => R.family.path.levels.clock.hatBeta K
local notation "w" => dosesAt R d (N:=N) (per:=per) file A.names A.turn
include station axes
theorem original (i:Fin n):
    (R.family.labels.level (d i)).coeffSize ((w) i)≤B*heat^power:=by
  let F:=R.family.labels.level (d i)
  let k₀:=((R.family.S.a K)^(d i))⁻¹
  let inner:=(doses R d file.station (N:=N) (per:=per) (file.A N per) A.names) i
  have scale:((R.family.S.a K:ℂ)^(d i))⁻¹=(k₀:ℂ):=by simp [k₀]
  have before:F.coeffSize ((k₀:ℂ) • inner)≤A.tuition*heat^power:=by
    rw [←scale]
    dsimp only [inner,doses]
    rw [←station,←axes]
    exact (A.fixed i).2.1
  have trueWord:(w) i=Motion.patch F (A.turn i) ((k₀:ℂ) • inner):=by
    rw [Motion.patch_smul,Motion.scalar_real]
    dsimp only [dosesAt,units]
    rw [scale]
  rw [trueWord]
  have nonneg:0≤Motion.orbitCost F:=(by linarith only [Motion.orbitCost_one_le F])
  calc
    _≤Motion.orbitCost F*F.coeffSize ((k₀:ℂ) • inner):=Motion.patch_cost F _ _
    _≤Motion.orbitCost F*(A.tuition*heat^power):=mul_le_mul_of_nonneg_left before nonneg
    _≤_:=by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right (A.priced i) (pow_nonneg (zero_le_one.trans (R.family.path.levels.fits.delayed K).le) _)

theorem weighted (S:Finset (Fin n)):
    (∑b:Selection R d S,‖weight R d N per K (w) S b‖)≤wallet R d (fun _=>B*heat^power) S:=
  WilsonReceivedCanonicalVersePortfolio.priced R d N per K kn (w) S _ (fun i _=>original R d file A station axes i)

end YM.Integration.WilsonPhysicalOrientedPivotSalary
end
