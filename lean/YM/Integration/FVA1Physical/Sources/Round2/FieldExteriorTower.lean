import YM.Integration.FVA1Physical.Round2.FieldExterior
import YM.Integration.FVA1Physical.Wilson.FluctuationPurchase

/-! Keep the signed cost of changing the retained field on the exterior
inside the true outer posterior. A good-chart estimate is then paid only
on that chart, and the complementary price involves the bounded physical
insertion, with no bound for the Wilson polynomial at remote fields. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open MeasureTheory Function Filter Set Lattice RG YM.Wilson Precision MSbar.Bulk
open YM.Integration.FVA1Physical.Wilson
open scoped Classical Topology
variable {G:Gauge} {c f:Side} {S:StepData c f} {R:Rep G f} (O:Config G c)
    {σ C δ Λ w:ℝ} (adm:Admitted O R S σ C δ Λ w)
include adm

theorem true_posterior_exterior {F Q:Config G f → ℝ} {copy:Config G f → Config G f} {H:Set (Config G f)}
    (live:MeasurableSet H) (mf:Measurable F) (mq:Measurable Q) (mc:Measurable copy)
    {K ε rare:ℝ} (K0:0 ≤ K) (ε0:0 ≤ ε) (bound:∀U,|F U| ≤ K)
    (outside:chance S R O Hᶜ ≤ rare) (regular:∀U∈H,|F (copy U)-Q (copy U)| ≤ ε) :
    let E:=expect S R O
    |E F-E (H.indicator (Q∘copy))| ≤ K*rare +
      |E (H.indicator (fun U=>F U-F (copy U)))|+ε := by
  intro E
  let d:=H.indicator (fun U=>F U-F (copy U))
  let I:=H.indicator (F∘copy)
  let W:=H.indicator (Q∘copy)
  have env:Envelope F:=⟨mf,K,bound⟩
  have envI:Envelope I:=Envelope.piece live ⟨mf.comp mc,K,fun U=>bound (copy U)⟩ (Envelope.const 0)
  have envd:Envelope d:=Envelope.piece live ⟨mf.sub (mf.comp mc),K+K,fun U=>
    (abs_sub _ _).trans (add_le_add (bound U) (bound (copy U)))⟩ (Envelope.const 0)
  have hsum:=e_sum O adm envd envI
  have eq:d+I=H.indicator F:=by
    funext U
    by_cases h:U∈H <;> simp [d,I,h,Function.comp_def]
  rw [eq] at hsum
  have hw:Measurable W := (mq.comp mc).indicator live
  have near: |E W-E I| ≤ ε := expect_difference adm hw envI fun U=>by
    by_cases hu:U∈H
    · simpa [W,I,hu,Function.comp_def,abs_sub_comm] using regular U hu
    simpa [W,I,hu] using ε0
  have bad:=expect_on_chart O live adm F mf K0 bound outside
  have eq2: E (H.indicator F)-E I=E d := by change _-_=expect S R O d; linarith only [hsum]
  have ni:|E I-E W| ≤ ε:=(abs_sub_comm _ _).le.trans near
  calc |E F-E W|≤|E F-E (H.indicator F)|+|E (H.indicator F)-E W|:=abs_sub_le ..
       _ ≤ K*rare+(|E (H.indicator F)-E I|+|E I-E W|):=add_le_add bad (abs_sub_le ..)
       _ ≤ K*rare+(|E d|+ε):=by rw [eq2]; exact add_le_add le_rfl (add_le_add le_rfl ni)
       _=_:=by ring

/-- At full torus coverage the signed exterior defect vanishes exactly if the
copied field is gauge equivalent to the original and the inserted posterior is
gauge invariant. This implication also applies to an exactly local insertion. -/
theorem true_posterior_copy_agrees {F Q:Config G f → ℝ} {copy:Config G f → Config G f} {H:Set (Config G f)}
    (live:MeasurableSet H) (mf:Measurable F) (mq:Measurable Q) (mc:Measurable copy)
    {K ε rare:ℝ} (K0:0 ≤ K) (ε0:0 ≤ ε) (bound:∀U,|F U| ≤ K) (outside:chance S R O Hᶜ ≤ rare)
    (same:∀U∈H,F U=F (copy U)) (regular:∀U∈H,|F (copy U)-Q (copy U)| ≤ ε) :
    |expect S R O F-expect S R O (H.indicator (Q∘copy))| ≤ K*rare+ε := by
  have q:=true_posterior_exterior O adm live mf mq mc K0 ε0 bound outside regular
  have eq:H.indicator (fun U=>F U-F (copy U))=fun _=>0 := by
    funext U; by_cases h:U∈H <;> simp [h,same]
  change _ ≤ K*rare+|expect S R O (H.indicator (fun U=>F U-F (copy U)))|+ε at q
  simpa only [eq,e_const O adm 0,abs_zero,add_zero] using q

end YM.Integration.FVA1Physical.Round2.Curvature
