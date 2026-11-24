import YM.Integration.WilsonCoherentInheritedRenderer
import YM.RGComparison.Core16.Spool.Wages
import YM.RGComparison.Core16.WilsonXLocal

/-! Every funded lamp supplies the analytic input and its own engineering
grade for the full older positive Wilson history. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentInheritedLamps
open Function PowerSeries Lattice Wilson RG Tree Precision
open PertExtension PertExtension.Series.Tested PertExtension.Chart
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Descent
open FVA2 FVA2.CityHistory
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice
open PhysicalNext.Repeat.Legato
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [Fintype I] {n c : Side}
variable (J : I → Lamp G) (o : I → Site n) (part : Bool)

omit [Fintype I] in
private lemma hot (i : I) (e : Edge Cover) :
    ContDiffAt ℝ ω (fun z : Edge (Site n) → G.Color =>
      G.mat (expandAt (o i) (expLinks G _ z) e)) 0 :=
  (G.exp_jet.comp (contDiff_apply ℝ G.Color (wrap n e.1+o i,e.2))).contDiffAt

theorem smooth :
    ContDiffAt ℝ ω ((look part ∘ tally J o) ∘ expLinks G (Edge (Site n))) 0 := by
  apply (look part).contDiff.contDiffAt.comp
  apply contDiffAt_prod
  intro i _
  obtain ⟨m,A,T,h,_⟩ := (J i).basis
  change ContDiffAt ℝ ω (fun z => (J i).action (expandAt (o i) (expLinks G _ z))) 0
  rw [h]
  exact Spool.signature (hot o i) A T

theorem registered (d : Descent n c) :
    d.Testable (look part ∘ tally J o) ∧ d.grade (look part ∘ tally J o) (power J) := by
  let coords := placement G d ∘ₗ (LinearMap.inl ℝ (Coordinates G d) (Pins G c))
  have entered (x : Coordinates G d) :
      (d.fine 1 ∘ d.tablePath) x=expLinks G _ (coords x) := by
    simpa [coords] using (placement_at (G:=G) (d:=d) (x,0))
  have chart : (look part ∘ tally J o) ∘ d.fine 1 ∘ d.tablePath =
      ((look part ∘ tally J o) ∘ expLinks G _) ∘ coords := funext (fun x=>congrArg _ (entered x))
  refine ⟨⟨(look part).continuous.comp (tally_cont J o),
    fun k U=> congrArg (look part) (tally_invariant J o k U),?_⟩,?_⟩
  · rw [chart]
    apply ContDiffAt.comp
    · rw [map_zero]
      exact (smooth J o part).of_le le_top
    · exact coords.toContinuousLinearMap.contDiff.contDiffAt
  · apply WilsonXLocal.wanted (look part)
    intro x
    let z := coords x
    let raw (i : I) (t : ℝ) := (J i).action (expandAt (o i) (expLinks G _ (t • z)))
    have item (i : I) : Bill (J i).order (raw i) := by
      obtain ⟨m,A,T,h,valuation⟩:=(J i).basis
      change Bill _ (fun t : ℝ => (J i).action (expandAt (o i) (expLinks G _ (t • z))))
      rw [h]
      exact Spool.shadow (hot o i) (by ext e; simp [expandAt,expLinks]) A _ T valuation z
    have whole : (fun t : ℝ => (tally J o ∘ d.fine 1 ∘ d.tablePath) (t • x)) =
        ∏ i,raw i := by
      funext t
      rw [Finset.prod_apply]
      change tally J o ((d.fine 1 ∘ d.tablePath) (t • x))=_
      rw [entered,map_smul]
      rfl
    rw [whole]
    exact bill_product _ _ _ (fun i _ => item i)

end YM.Integration.WilsonCoherentInheritedLamps
end
