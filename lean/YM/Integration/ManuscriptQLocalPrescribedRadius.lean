import YM.Integration.ManuscriptQLocalRegularCalendar
import YM.Integration.ManuscriptQLocalBarePackets

/-! The two marker circles and the original, unmodified marked coupling columns. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalPrescribedRadius
open Filter Lattice Wilson RG Marker Comparison.RG02
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric PhysicalNext.Repeat.Legato Pert.Asymptotics
open ManuscriptQLocalRegularConditional ManuscriptQLocalOriginalConditionalTail
open scoped Classical BigOperators Topology

def radius (geometry : ℝ) (weight : ℕ) : ℝ := (2*geometry^weight)⁻¹

theorem collar {geometry g : ℝ} (h : 1≤geometry) (hg : 0<g) (w : ℕ) :
    0<radius geometry w ∧ 2*(radius geometry w/g)≤g⁻¹ := by
  have hw := one_le_pow₀ h (n:=w)
  have hp : 0<geometry^w := zero_lt_one.trans_le hw
  constructor
  · exact inv_pos.mpr (by positivity)
  · rw [←one_div g,←mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hg.le
    change 2*(2*geometry^w)⁻¹≤1
    rw [←div_eq_mul_inv,div_le_one (by positivity)]
    linarith

variable {G : Gauge} {V : Type} {C : Family G} {J : Request V}

/-- A fixed rooted amplitude of fee `geometry^d`, summed at the larger purchased disk,
    returns its requested order after all powers in the prescribed marker radius are restored. -/
theorem drawn (A : NumericSchedule C J) (d w q : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∃ start : ℕ,∀ m, start≤ m→∀ N p : ℕ,m<N→let g:=regulatorRun C N p (m+1);
      0 < g → g ≤ 1 → A.admittedCost m^d*(g/radius (A.admittedCost m) w)^q≤
        2^q*g^((q:ℝ)-δ) := by
  obtain ⟨start,spend⟩ := ManuscriptQLocalRegularCalendar.absorb A (d+w*q) q δ hδ
  refine ⟨start,fun m hm N p hN hg weak=>?_⟩
  let g:=regulatorRun C N p (m+1)
  have exchange : A.admittedCost m^d*(g/radius (A.admittedCost m) w)^q =
      2^q*(A.admittedCost m^(d+w*q)*g^q) := by
    simp only [radius,div_inv_eq_mul,mul_pow,pow_add,pow_mul]
    ring
  rw [exchange]
  exact mul_le_mul_of_nonneg_left (spend m hm N p hN hg weak) (pow_nonneg (by norm_num) _)

variable [DecidableEq V] [Fintype V] (Γ : Census V) (R : Run G) (hG : G.Simple)
  (A : NumericSchedule R.family J)

include hG in
/-- Every finite coefficient here uses the independently appointed source's own powers and ranks. -/
theorem original (k : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ m : ℕ in atTop,∀ (d : LocalFormal.Datum R.family Γ),d.level=m→
      ∀ (F : AnalyticInput J A d),ManuscriptQLocalOriginalSourceGrade.Bare F→
      ∀ (x : IndependentTests J.tests) (U : Config G (R.family.side d.level d.period)) (s : Γ.Mode),
      let g:=regulatorRun R.family d.cutoff d.period (d.level+1)
      let p₀:=(R.family.path.rep d.cutoff d.period (d.level+1)).p
      let ℓ:=ManuscriptQLocalShiftLedger.weight (fun _:V=>F.packets.powerCap+F.packets.rankCap) s
      let L z:=Extra.Trajectories.connected (moment R.family (N:=d.cutoff) U (source F.packets p₀ g x) z)
      ∃p : Polynomial ℂ,p.natDegree≤ℓ ∧ (∀z,p.eval z=(L z).part s) ∧
        Poly.toll (fun v=>F.inputRadii v/F.kernelCosts v) s*‖(L 1).part s-ManuscriptQLocalConditionalGradeTail.low p ℓ k‖≤
          ManuscriptQLocalRegularCalendar.constant (J:=J) Γ*g^((k+1:ℕ)-δ:ℝ) := by
  filter_upwards [ManuscriptQLocalRegularCalendar.purchased Γ R hG A k hδ] with m paid d hd F bare x U s
  exact paid d hd F F.packets bare F.power_bounded F.rank_bounded x U s

end YM.Integration.ManuscriptQLocalPrescribedRadius
end
