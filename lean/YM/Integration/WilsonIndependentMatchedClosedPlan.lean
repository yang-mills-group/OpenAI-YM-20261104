import YM.Integration.WilsonIndependentMatchedRankedPair

/-! Releasing a finite gauge observable at the unconditioned root needs
only its original gauge, continuity and canonical cotree germ. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedClosedPlan
open Function Lattice Wilson PertExtension PertExtension.Chart RegulatorIR RegulatorIR.Geometry
open RegulatorIR.Binding RegulatorIR.Laplace XSpace FVA2 PowerSeries
open WilsonIndependentMatchedOrbitReading
open scoped Classical ContDiff
variable {G:Gauge}{R:XSpace.Period}

theorem actual {n:Side}(he:Even n.val)(O:Config G n→ℝ)(h:Orb.PreTest O):
    Plan G n (insert O) := by
  refine ⟨?_,?_,?_⟩
  · intro k hk u t
    change O (orbLift (goat k u))=O (orbLift u)
    rw [goat_lift k u hk,h.gauge _ hk]
  · have links:Continuous (Orb.liftLinks (K:=G.El) (n:=n)) := by
      apply continuous_pi
      intro e
      unfold Orb.liftLinks
      split <;> fun_prop
    exact (h.continuous.comp links).comp (continuous_fst.comp continuous_snd)
  · change ContDiffAt ℝ ∞ (fun z:Meadow G Empty × ℝ × Meadow G (Orb.OEdge n)=>
      O (Orb.liftLinks (Chart.expLinks G _ z.2.2))) 0
    apply OrbGerm.adapt he h
    intro i
    apply OrbGerm.AtBase.exp (f:=fun z:Meadow G Empty × ℝ × Meadow G (Orb.OEdge n)=>z.2.2 i)
    · fun_prop
    · rfl

theorem product {n:Side}{O P:Config G n→ℝ}(ho:Orb.PreTest O)(hp:Orb.PreTest P):
    Orb.PreTest (O*P) := by
  refine ⟨fun k hk U=>by change O _ *P _=O _ *P _; rw [ho.gauge _ hk,hp.gauge _ hk],
    ?_,ho.continuous.mul hp.continuous⟩
  exact ⟨ho.curved.boundedness.mul hp.curved.boundedness,ho.curved.germ.mul hp.curved.germ⟩

theorem pair (T:R.Tree){O P:Config G R.side→ℝ}(ho:Orb.PreTest O)(hp:Orb.PreTest P)
    {A B:Bare.Series T G}{r s q:ℕ}
    (left:PowerSeries.X^r*A=BareOrb.stencil T O)
    (right:PowerSeries.X^s*B=BareOrb.stencil T P):
    coeff q (Bare.normalized T G (A*B))=
      (plotPT originalClock (insert (O*P)) (r+s) q:ℂ) :=
  WilsonIndependentMatchedRankedPair.pair T O P ho hp (product ho hp)
    (actual (even_iff_two_dvd.mpr R.even) _ (product ho hp)) left right

end YM.Integration.WilsonIndependentMatchedClosedPlan
end
