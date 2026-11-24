import YM.Integration.FVA1Physical.Round2.FieldExterior
import YM.Integration.FVA1Physical.Wilson.FluctuationPurchase

/-! The interacting physical trajectory pays its change of variables, the
discarded conditional fibres and the genuine posterior normalization before
the observable and the polynomial to compare it to are selected. -/
set_option autoImplicit false
set_option maxHeartbeats 1100000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Lis MSbar.Midpoint MSbar.Wave MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock
open MSbar.Bulk MSbar.Whisk MSbar.Rolling MSbar.Cacao MSbar.Mosaic RGComparison.Core16
open Push Push.Uniform SectorNext.Vacuum YM.Integration.FVA1Physical.Wilson
open scoped Classical Topology
variable {G : Gauge}

theorem fluctuation_field_exterior (J : Voice G) (cle : Clear G J) (simple : G.Simple)
    (H H' : Stage) (P : Patch) (K : KernelChoices) (branch : P.Branches K G)
    {D q : ℝ} (hD : 0 ≤ D) (hq : 0 < q) :
    ∀ᶠ x : ℝ in atTop, ∀ (A : Mosaic.Issue G), A.S.patch=P → A.S.kernel=K →
      Season J H H' x A.pre A.post A.S (courage G P.L x) →
      ∀ (z : Positions (Primary A.c G)) (b : Site A.f), ‖z‖ ≤ D*room (tip G P.L x) →
      let y:=tip G P.L x; let X:=boxX y b; let Y:=boxY y b
      let O:=represent (tint G (Exterior.Body 1 A.c) z)
      let μ:=vest (priced A.F A.v A.pre.clip A.pre.path) z
      let U:=hotel A.F X Y J O μ (pillow y) (room y)
      let law:=woolModel A.F X J A.pre Y A.v O μ (pillow y) (room y)
      ∀ (φ : Config G A.f → ℝ), GaugeLocal A.S (youth A.F Y) φ → (∀ Z, |φ Z| ≤ 1) →
      ∀ (W ε : ℝ), 0 ≤ ε → (∀ Z ∈ U, |Rota.resample A.F (board A.F X) law U φ Z-W| ≤ ε) →
      |expect A.S A.pre O φ-W| ≤ 2*ε+10*y^(-q) := by
  obtain ⟨p,buy⟩ := purchased_fluctuation_chance J cle simple H H' P K branch hD (-q)
  by_cases ok : 0 < p.gap ∧ 0 < p.a ∧ 0 < p.density
  swap
  · filter_upwards [buy] with x offer
    intro A hp hk season z b hz
    have h := (offer A hp hk season z b hz).1.buys
    exact False.elim (ok ⟨h.pos_m,h.pos_a,h.pos_C⟩)
  have rise := Work.E09.betaF_growth G P.L
  have shrink := (tendsto_rpow_neg_atTop hq).comp rise
  filter_upwards [buy,solders P K J H H' p cle ok.1 ok.2.1 ok.2.2, rise.eventually_gt_atTop 0,
    shrink.eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1/2))] with x offer shield positive small
  intro A hp hk season z b hz y X Y O μ U law φ localφ unit W ε hε inside
  obtain ⟨_,cal,_,_⟩ := offer A hp hk season z b hz
  have pc := season.case_
  rw [hp] at pc
  have bloom := (shield A.pre A.post pc season.hull).holm
  have mass : 0 < A.S.push A.pre.beta A.pre.eval O := by
    rw [←season.taskEval]
    unfold Rep.eval
    rw [Activities.gas_one _ _ (voids cal.first.folds bloom),mul_one]
    exact Real.exp_pos _
  have adm : Admitted O A.pre A.S H'.width H'.paths (ability y) (lbt y) 1 :=
    ⟨pc.lawful,fun U=>(season.shine U).le,mass,A.S.isKernel season.bends.1 _⟩
  obtain ⟨_,_,rot⟩ := cal.rain
  have tact:=cal.turn
  rw [Real.rpow_zero] at tact
  exact exterior_field_average O rot.reforms.from_here adm rot tact cal.sails
    (Real.rpow_nonneg positive.le _) small localφ unit W hε inside

end YM.Integration.FVA1Physical.Round2.Curvature
