import YM.Integration.WilsonOlderFreshGraphSchool
import YM.FormalBulk08.Borough.Mint
import YM.FormalBulk08.Rift.Glory

/-! Original finite-graph position salary at the chosen physical school's root.
The three copies of the exhibited tour cover the word itself and a spare
strip for its two physical masks. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOlderFreshGraphTours
open RG Precision Wilson Lattice FormalBulk08 Reef Lava Lotus Shore Mesa Gorge Rift Borough
open QuadraticLocal QuadraticLocal.Mentor AllOrder.Floe.Step.PlanV
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.Foundations Push.PriceCompiler
open WilsonOlderFreshGraphSchool
open scoped ENNReal NNReal BigOperators Classical

def signedMenu (G:Gauge) (shell:ℕ→ℝ) (pos:∀k,0<shell k) : Menu where
  width := fun _ _ K _ x=>(windowBasis G K).width x
  positive := fun _ _ K _ x=>(windowBasis G K).pos x
  shell := shell
  cost := pos

def fee (b:ℝ) (m:ℕ):ℝ := (m.factorial:ℝ) / (b/2)^m * Real.exp b

private theorem kernel {b c σ:ℝ} (hb:0<b) (hc:0<c) (hs:0≤σ) (gate:σ≤b/(16*c))
    (D len m:ℕ) (route:(len:ℝ)≤c*(1+(D:ℝ))) :
    (1+(D:ℝ))^m * Real.exp (3*σ*(len:ℝ)) ≤ fee b m * Real.exp (b*(D:ℝ)) := by
  let a:=b/2
  have ha:0<a:=half_pos hb
  have path:0≤1+(D:ℝ):=by positivity
  have fac:0<(m.factorial:ℝ):=by positivity
  have apow:0<a^m:=pow_pos ha m
  have seed:σ*(16*c)≤b:=(le_div_iff₀ (by positivity)).mp gate
  have hnorm: (1+(D:ℝ))^m ≤ Real.exp (a*(1+(D:ℝ)))*(m.factorial:ℝ)/a^m := by
    apply (le_div_iff₀ apow).mpr
    have h:= (div_le_iff₀ fac).mp (Real.pow_div_factorial_le_exp _ (mul_nonneg ha.le path) m)
    simpa only [mul_pow, mul_comm (a^m)] using h
  have linear:3*σ*(len:ℝ)≤a*(1+(D:ℝ)) := by
    calc
      _≤(3*σ)*(c*(1+(D:ℝ))):=mul_le_mul_of_nonneg_left route (by positivity)
      _=(3*σ*c)*(1+(D:ℝ)):=by ring
      _≤a*(1+(D:ℝ)):=mul_le_mul_of_nonneg_right (by dsimp [a];nlinarith [mul_nonneg hs hc.le]) path
  calc
    _≤(Real.exp (a*(1+(D:ℝ)))*(m.factorial:ℝ)/a^m)*Real.exp (3*σ*(len:ℝ)) :=
      mul_le_mul_of_nonneg_right hnorm (Real.exp_pos _).le
    _=(m.factorial:ℝ)/a^m*Real.exp (a*(1+(D:ℝ))+3*σ*(len:ℝ)):=by rw [Real.exp_add]; ring
    _≤(m.factorial:ℝ)/a^m*Real.exp (b+b*(D:ℝ)):=by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      dsimp [a] at linear ⊢;linarith
    _=fee b m*Real.exp (b*(D:ℝ)):=by rw [Real.exp_add];dsimp [fee,a];ring

theorem enrolled {G:Gauge} (hG:G.Simple) (R:Run G) (φ:ℕ→ℕ) (shell:ℕ→ℝ) (pos:∀k,0<shell k)
    (k x:ℕ) (late:1≤k) {V:Type*} (D:Reach V) (o:V) {r:ℕ} (T:Tile V r) (C:ℝ)
    (before:Knoxville D ((windowBasis G R.family.path.levels.clock.kernel).width x) o T C)
    (len:chain V r→ℕ) (route:∀v,(len v:ℝ) ≤ shell k*(1+(wide D (Fin.cons o v : chain V (r+1)):ℝ))) (m:ℕ):
    let b:=(windowBasis G R.family.path.levels.clock.kernel).width x
    let σ:=Poetry.Agenda.seed (roots (signedMenu G shell pos) hG R.metals.p R.metals.K) φ k x
    (∑' v:chain V r, ENNReal.ofReal ((1+(wide D (Fin.cons o v : chain V (r+1)):ℝ))^m *
       Real.exp (3*σ*(len v:ℝ))) * ‖T v‖ₑ)≤ ENNReal.ofReal (fee b m * C) := by
  intro b σ
  have bpos:0<b:=(windowBasis G _).pos x
  have σpos:0<σ:=Poetry.Agenda.stem _ _ _ _
  have idK:R.family.path.levels.clock.kernel = R.metals.p.kernel:=R.alloy.B.valid.kernel
  have small:σ≤b/(16*shell k):=by
    dsimp only [b]; rw [idK]
    exact WilsonOlderFreshGraphStrip.narrow hG R.metals.p.profile R.metals.K R.metals.p.kernel
      (fun _ l=>(windowBasis G R.metals.p.kernel).width l) shell (fun _ l=>(windowBasis G _).pos l) pos φ k x late
  have fpos:0≤fee b m:=by unfold fee;positivity
  calc
    _≤∑' v:chain V r,ENNReal.ofReal (fee b m) * (Gorge.shine b (wide D (Fin.cons o v : chain V (r+1))) * ‖T v‖ₑ) := by
      apply ENNReal.tsum_le_tsum; intro v
      rw [←mul_assoc, Gorge.shine, ←ENNReal.ofReal_mul fpos]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (kernel bpos (pos k) σpos.le small _ _ m (route v))) _
    _=ENNReal.ofReal (fee b m) * ∑' v:chain V r,(Gorge.shine b (wide D (Fin.cons o v : chain V (r+1))) * ‖T v‖ₑ):= ENNReal.tsum_mul_left
    _≤ENNReal.ofReal (fee b m) * ENNReal.ofReal C:= mul_le_mul_right before.2 _
    _=ENNReal.ofReal (fee b m*C):=(ENNReal.ofReal_mul fpos).symm

end YM.Integration.WilsonOlderFreshGraphTours
end
