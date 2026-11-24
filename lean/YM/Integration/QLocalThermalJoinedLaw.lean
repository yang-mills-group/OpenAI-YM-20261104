import YM.Integration.QLocalThermalJoinedSource
import YM.Integration.QLocalMarkedJoinedEligibility

/-! The source used in each new compulsory row is the original paid
physical path token, restricted by the actual flags in its own footprint. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalThermalJoinedLaw
open Function Finset Set MeasureTheory Lattice Wilson RG Marker Overlay
open Next.Foundations Extra.Iteration LocalComparison Comparison.Density.RenderM LocalComparison.MarkedPackets
open QLocalThermalPacketDivision QLocalThermalJoinedSource QLocalMarkedJoinedEligibility
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {Q:Rep G n} {V:Type} [DecidableEq V] [Fintype V]
    {D:V→ ComparisonDensity.Address.Orbit} {Γ:Census V} (P:MarkedPackets D G n Γ)
    {p:BudgetPoint} {a:V→Support n} {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width budget:ℝ} {off cov:ℕ}

theorem smooth {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V]
    {D:V→ ComparisonDensity.Address.Orbit} {Γ:Census V} (P:MarkedPackets D G n Γ)
    {p:BudgetPoint} {a:V→Support n} {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width budget:ℝ} {off cov:ℕ} (H:P.Paid p a region w g width budget off cov) (i:ℕ)
    (T:Token G n (fun v=>(D v).Mood) (P.rank i)) (active:P.packet i=some T) (x:TestSpace D) (q:BudgetPoint) :
    q.Regular T.plot (T.read x) := by
  have real:(T.re x).Invariant:=fun h B=>by
    rw [←(T.real_and_imag ..).1,H.symmetry i T active x B h,(T.real_and_imag ..).1]
  have imag:(T.im x).Invariant:=fun h B=>by
    rw [←(T.real_and_imag ..).2,H.symmetry i T active x B h,(T.real_and_imag ..).2]
  rw [T.reading x]
  exact regular_larger (regular_add (AnalyticBridge.VerifiedReset.regular_mapped Complex.ofRealCLM (Derivs.canonical_regular _ _ _ real))
    (regular_smul _ (AnalyticBridge.VerifiedReset.regular_mapped Complex.ofRealCLM (Derivs.canonical_regular _ _ _ imag))))
    (H.paths i T active x).2

theorem legible (H:P.Paid p a region w g width budget off cov) (x:TestSpace D) (i:ℕ) :
    LocalOn (plot P i) (fun U=>P.term x g U i) ∧ GaugeInvariant (fun U=>P.term x g U i) ∧
      Measurable (fun U=>P.term x g U i) := by
  cases e:P.packet i with
  | none=>simpa [plot,MarkedPackets.term,e] using
      (show LocalOn (∅:Support n) (fun _:Config G n=>(0:ℂ)) ∧
        GaugeInvariant (fun _:Config G n=>(0:ℂ)) ∧ Measurable (fun _:Config G n=>(0:ℂ)) from
        ⟨fun _ _ _=>rfl,fun _ _=>rfl,measurable_const⟩)
  | some T=>
    let reg:=smooth P H i T e x p
    simp only [plot,MarkedPackets.term,e,Option.elim_some]
    exact ⟨fun U V same=>congrArg ((g:ℂ)^P.power i*·) (reg.sites U V same),
      fun k U=>congrArg ((g:ℂ)^P.power i*·) (reg.symmetry k U),measurable_const.mul reg.borel⟩

theorem charged (H:P.Paid p a region w g width budget off cov) (o:V→Site n) (point:∀v,o v∈a v)
    (s:Γ.Mode) (x:TestSpace D) (c:ℂ) :
    Law (W:=Q) (Y:=plot P) o s (row P Q.p g c s x) := by
  have choose (U:Config G n) (i:ℕ):pick P Q.p U i≠none ↔ ¬Healthy Q.p.threshold (plot P i) U:=
    not_congr (healthy P Q.p U i)
  refine ⟨?_,?_,?_,?_⟩
  · intro i U nz v hv
    have mode:s=P.mode i:=by by_contra bad; exact nz (by simp [row,bad])
    cases e:P.packet i with
    | none=>exact False.elim (nz (by simp [row,MarkedPackets.term,e]))
    | some T=>simpa [plot,e] using (H.addresses i T e v (mode ▸ hv)) (point v)
  · intro i U Z data flags
    have chosen:pick P Q.p U i=pick P Q.p Z i:=congrArg first flags
    simp only [row,chosen,(legible P H x i).1 U Z data]
  · intro i k U
    simp only [row,pick,gauge_flags,(legible P H x i).2.1 k U]
    split_ifs <;> rfl
  · intro i
    by_cases mode:s=P.mode i
    · have clean:MeasurableSet {U:Config G n|Healthy Q.p.threshold (plot P i) U}:=by
        simpa only [Healthy,Finset.disjoint_iff_inter_eq_empty] using
          (ActualWilsonTaylorSlot.guard_measurable (G:=G) (∅:Support n) (plot P i) Q.p.threshold)
      have meas:Measurable (fun U:Config G n=>if ¬Healthy Q.p.threshold (plot P i) U
          then c*P.term x g U i else 0):=(measurable_const.mul (legible P H x i).2.2).ite clean.compl measurable_const
      have eq : row P Q.p g c s x i=(fun U=>if ¬Healthy Q.p.threshold (plot P i) U then c*P.term x g U i else 0) := by
        funext U
        simp [row,mode,choose]
      rw [eq]
      exact meas
    · have eq : row P Q.p g c s x i=(fun _:Config G n=>(0:ℂ)) := by
        funext U
        simp [row,mode]
      rw [eq]
      exact measurable_const

end YM.Integration.QLocalThermalJoinedLaw
