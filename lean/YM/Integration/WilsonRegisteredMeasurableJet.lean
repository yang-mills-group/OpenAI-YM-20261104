import YM.Integration.WilsonRegisteredAffineTaylor
import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Borel

/-! Measurable real coordinates for the signed Taylor polynomial of an old
Wilson row. The same finite derivative at the genuine pivot is recovered
on its original regular domain. No regularity away from that domain is
required to place the coordinate in the experiment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredMeasurableJet
open Filter MeasureTheory Function Finset Lattice Wilson RG Push.Local
open AnalyticBridge.MarginalMultiplier3b1d
open private tick scanD from YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Borel
open scoped Classical
variable {G:Gauge} {n:Side} {Ω:Type*} [MeasurableSpace Ω]

private theorem coefficient (f:Config G n→ℝ) (hf:Measurable f) (D:Ω→Directions G n) (hd:Measurable D)
    (j:ℕ) (W:Ω → Config G n) (hw:Measurable W) :
    Measurable (fun z=>scanD f (List.replicate j (D z)) (W z)):=by
  induction j generalizing W with
  | zero=>exact hf.comp hw
  | succ j ih=>
    simp only [List.replicate_succ,scanD]
    apply StronglyMeasurable.measurable ∘ StronglyMeasurable.limUnder
    intro i
    have scaled:Measurable (fun z=>tick i • D z):=hd.const_smul (tick i)
    have ex:Measurable (PertExtension.Chart.expLinks G (Edge (Site n))):=PertExtension.Chart.expLinks_meas
    have inc:Measurable (fun z=>increment (W z) (tick i • D z)):=(ex.comp scaled).mul hw
    exact (((ih _ inc).sub (ih W hw)).div_const _).stronglyMeasurable

def printed (η:ℂ→L[ℝ]ℝ) (F:Config G n→ℂ) (W:Config G n) (D:Directions G n) (q:ℕ) (r:ℝ):ℝ :=
  ∑ j∈range (q+1),((j.factorial:ℝ)⁻¹*r^j)*scanD (η ∘ F) (List.replicate j D) W

theorem measured (η:ℂ→L[ℝ]ℝ) (F:Config G n→ℂ) (hf:Measurable F)
    (W:Ω → Config G n) (mw:Measurable W) (D:Ω→Directions G n) (md:Measurable D)
    (q:ℕ) (r:ℝ) : Measurable fun z=>printed η F (W z) (D z) q r := by
  exact Finset.measurable_sum _ fun j _=>measurable_const.mul
    (coefficient (η ∘ F) (η.continuous.measurable.comp hf) D md j W mw)

theorem original {p:BudgetPoint} {Y:Support n} {F:Config G n→ℂ} (η:ℂ→L[ℝ]ℝ)
    (W:Config G n) (D:Directions G n) (q:ℕ) (r:ℝ) (reg:p.Regular Y F)
    (clean:Healthy p.threshold Y W) (hq:q ≤ p.order) :
    printed η F W D q r=η (WilsonRegisteredAffineTaylor.jet F W D q r) := by
  simp only [printed,WilsonRegisteredAffineTaylor.jet,map_sum,map_smul,smul_eq_mul]
  apply sum_congr rfl
  intro j hj
  let l:=List.replicate j D
  have length:l.length ≤ p.order:=by rw [List.length_replicate];exact (Nat.le_of_lt_succ (mem_range.mp hj)).trans hq
  have chart:Push.Local.Chart p.order F W:=reg.smooth W clean
  have real:Push.Local.Chart l.length (η ∘ F) W:=
    η.contDiff.contDiffAt.comp _ (chart.of_le (by exact_mod_cast length))
  rw [show scanD (η ∘ F) (List.replicate j D) W=_ from scanD_eq l real,
    show leftDerivs (η ∘ F) l W=_ from left_linear η l chart length]

end YM.Integration.WilsonRegisteredMeasurableJet
end
