import YM.Integration.WilsonPositionProgramPublicWickGram
import YM.Integration.WilsonOriginalPublicPivotRoster
import YM.Integration.WilsonOriginalPublicPivotSurvey

/-! A finite, uncentered reflected hearing prices the complete evaluated
coefficient vector. All stochastic inputs are numerical signed readings of the
same source. The finite Wilson bank is evaluated on each of its actual boards. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 550000
namespace YM.Integration.WilsonOriginalPublicPivotReflected
open Filter Finset Function Lattice RG Wilson Labels PhysicalNext.Repeat.Legato PowerSeries
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open Source MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonPositionProgramPublicWickGram (nodes reading)
open WilsonPositionProgramPublicContrast (assay)
open WilsonThermometerPositionTunedSlope (paid finite)
open WilsonPositionProgramTrialThermalGrades (frozen)
open scoped Classical BigOperators
variable {G:Gauge}{h n:ℕ}{I:Type} [Fintype I] {B:Local.Physical.Deck G}

theorem absorption {k x u z e t c:ℝ} (kp:0<k)(xp:0≤x)(_up:0≤u)(zp:1≤z)(cp:0≤c)
    (mixed:e*u≤1)(twice:e*u^2≤1)(tail:t≤1)
    (hearing:k*x^2≤c*z^2+1+e*(2*u*x+u^2)+t):
    x≤ max 1 ((c+5)/k)*z:=by
  have small:k*x^2≤c*z^2+2*x+3:=by
    have eu:=mul_le_mul_of_nonneg_right mixed xp
    nlinarith only [hearing,eu,twice,tail]
  by_cases low:x≤z
  · exact low.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 ((c+5)/k)) (zero_le_one.trans zp))
  · have zx:z≤x:=le_of_not_ge low
    have x0:0<x:=zero_lt_one.trans_le (zp.trans zx)
    have m:c*z^2≤c*z*x:=by rw [pow_two,←mul_assoc];exact mul_le_mul_of_nonneg_left zx (mul_nonneg cp (zero_le_one.trans zp))
    have a:x≤z*x:=by simpa only [one_mul] using (mul_le_mul_of_nonneg_right zp xp)
    have b:1≤z*x:=zp.trans (zx.trans a)
    have xx:k*x≤(c+5)*z:=(mul_le_mul_iff_of_pos_right x0).mp (by nlinarith only [small,a,b,m])
    calc
      x ≤ ((c+5)/k)*z:=by rw [div_mul_eq_mul_div];exact (le_div_iff₀ kp).mpr (by linarith only [xx])
      _ ≤ _:=mul_le_mul_of_nonneg_right (le_max_right ..) (zero_le_one.trans zp)

def evaluated (q:ℕ) (g:ℝ) (Y:PowerSeries ℂ):ℂ:=∑k∈Finset.Iic q,(g:ℂ)^k*coeff k Y

def board (R:Run G)(W:Initialize G)(d:Fin n→ℕ)(v:(i:Fin n)→(R.family.labels.level (d i)).Coeff)
    (X:Sample n)(S:Finset (Fin n)):PowerSeries ℂ:=
  paid R (d ∘ Subtype.val:S→ℕ) (frozen R (d ∘ Subtype.val:S→ℕ) (fun i:S=>v i))
    (finite R (d ∘ Subtype.val:S→ℕ) X.F.p (fun i:S=>X.layout i) (W.tree X.F.p))

/-- The full ordered sum on the nominated finite boards, including the selected
common center, the true registered coefficients and the full vacuum division. -/
def sampled {M:Type*} [Fintype M] (R:Run G)(W:Initialize G)(d:Fin n→ℕ)
    (v:(i:Fin n)→(R.family.labels.level (d i)).Coeff) (X:M→Sample n) (μ:M→ℂ)
    (S:Finset (Fin n))(q:ℕ)(g:ℝ):ℂ:=∑a,μ a*evaluated q g (board R W d v (X a) S)

theorem original (R:Run G)(W:Initialize G)(axis:Axis)(leg:I→Glyph B h)(entire:Injective leg):
    ∃k τ:ℝ,0<k ∧ 0<τ ∧
    ∀ {M:Type} [Fintype M] (d:Fin 2→ℕ) (v:(i:Fin 2)→(R.family.labels.level (d i)).Coeff)
      (X:M→Sample 2)(μ:M→ℂ)(q:ℕ)(g:ℝ)(coarse:ℂ)(G₀:I→I→ℂ)(a:I→ℂ)
      (c z u e t:ℝ), 0≤c → 1≤z → 0≤u → e*u≤1 → e*u^2≤1 → t≤1 →
      ‖G₀-reading axis (nodes axis) leg‖≤τ → ‖coarse‖≤c*z^2 →
      ‖sampled R W d v X μ univ q g-coarse‖≤1 →
      ‖assay a a G₀-sampled R W d v X μ univ q g‖≤e*(2*u*‖a‖+u^2)+t →
      ‖a‖≤ max 1 ((c+5)/k)*z:=by
  obtain ⟨k,τ,kp,tp,rank⟩:=WilsonPositionProgramPublicWickGram.original axis leg entire
  refine ⟨k,τ,kp,tp,?_⟩
  intro M inst d v X μ q g coarse G₀ a c z u e t cp zp up first both last near wc phys split
  apply absorption kp (norm_nonneg _) up zp cp first both last
  let y:=sampled R W d v X μ univ q g
  have pay:‖y‖≤c*z^2+1:=by
    calc
      _ ≤ ‖y-coarse‖+‖coarse‖:=by simpa only [sub_add_cancel] using norm_add_le (y-coarse) coarse
      _ ≤ _:=by linarith only [phys,wc]
  calc
    k*‖a‖^2 ≤ ‖assay a a G₀‖:=rank G₀ near a
    _ ≤ ‖assay a a G₀-y‖+‖y‖:=by simpa only [sub_add_cancel] using norm_add_le (assay a a G₀-y) y
    _ ≤ _:=by linarith only [split,pay]

end YM.Integration.WilsonOriginalPublicPivotReflected
end
