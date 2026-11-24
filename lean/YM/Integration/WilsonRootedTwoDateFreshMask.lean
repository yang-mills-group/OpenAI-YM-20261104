import YM.Integration.QLocalThermalPacketDivision
import YM.Integration.WilsonRootedTwoDateCoolingRows

/-! Identification of the physical packet's clean and flagged splits on every gauge configuration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateFreshMask
open Push.Local Push.AbsoluteSums
open Function Finset Lattice Wilson RG Marker LocalComparison LocalComparison.MarkedPackets
open Comparison.Density.RenderM ManuscriptQLocalOriginalConditionalTail QLocalThermalPacketDivision
open scoped Classical BigOperators
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {n : Side}
    {D : V → ComparisonDensity.Address.Orbit} (P : MarkedPackets D G n Γ)

theorem clear_source (p : BudgetPoint) (g : ℝ) (x : IndependentTests D) (U : Config G n) :
    clear P p (testInclusion D x) g U=source P p g x 1 U := by
  let clean := WilsonPrescribedPacketTail.slice P (fun i=>pick P p U i=none)
  have on_live (i : Live P) : clean.term (testInclusion D x) g U i=field P p g x i U := by
    have plot_eq : plot P i=(token P i).plot := by simp [plot,chosen P i]
    by_cases h : Healthy p.threshold (token P i).plot U
    · have keep := (QLocalThermalPacketDivision.healthy P p U i).2 (plot_eq.symm ▸ h)
      rw [field,masked_eq _ _ _ _ h]
      simp [clean,WilsonPrescribedPacketTail.slice,MarkedPackets.term,keep,chosen P i]
    · have drop : pick P p U i≠none := fun e=>h (plot_eq ▸ (QLocalThermalPacketDivision.healthy P p U i).1 e)
      rw [field,masked_ne _ _ _ _ h]
      simp [clean,WilsonPrescribedPacketTail.slice,MarkedPackets.term,drop]
  rw [physical]
  change (∑'i:ℕ,Poly.send (P.mode i) (clean.term (testInclusion D x) g U i))=_
  symm
  calc
    _=∑'i:Live P,Poly.send (P.mode i) (clean.term (testInclusion D x) g U i) :=
      tsum_congr (fun i=>congrArg (Poly.send (P.mode i)) (on_live i).symm)
    _=_ := by
      apply tsum_subtype_eq_of_support_subset (s:={i:ℕ | (P.packet i).isSome})
        (f:=fun i:ℕ=>Poly.send (P.mode i) (clean.term (testInclusion D x) g U i))
      intro i hi
      cases e : P.packet i with
      | none=>exact (hi (by simp [clean,WilsonPrescribedPacketTail.slice,MarkedPackets.term,e])).elim
      | some t=>change (P.packet i).isSome;simp [e]

variable {q : BudgetPoint} {a : V→Support n} {region : Comparison.Density.Testing.Region (fun i=>(D i).Mood) n}
    {w : V→ℝ} {g width budget : ℝ} {off cov : ℕ}

theorem dirty_source (p : BudgetPoint) (H : P.Paid q a region w g width budget off cov) (hg : g≠0)
    (x : IndependentTests D) (U : Config G n) : dirty P p (testInclusion D x) g U=
      P.read (testInclusion D x) g U-source P p g x 1 U := by
  have split := (partition P p H hg (testInclusion D x) U).2
  rw [clear_source] at split
  rw [←split]
  abel

end YM.Integration.WilsonRootedTwoDateFreshMask
