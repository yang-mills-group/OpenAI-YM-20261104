import YM.Integration.WilsonIndependentMatchedOpeningCensus
/-! A common nonconstant scalar formal coefficient may be attached to an authentic word at the opening. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOpeningFee
open Function Filter Finset PowerSeries Lattice RG Wilson Tree Source Labels
open Laurent Bloch Metric FreeResolvent Work.F08 Precision Exterior Gauge XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Bank
open WilsonCoeffUV.Wheel.Flooring PertExtension RegulatorIR RegulatorIR.Budget
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedSectionIncome (leaf)
open WilsonIndependentMatchedOrdinarySeat (here received)
open WilsonIndependentSpoutOrdinaryPlate (sample)
open scoped Classical BigOperators
open WilsonIndependentMatchedTopReceipt (realDose)
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonIndependentMatchedOpeningRoster (seat)
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonIndependentMatchedOrdinarySeat (ground)
variable {G:Gauge}{h:ℕ}
theorem natural {U:Type}(t:ℝ→ₗ[ℝ]ℝ)(a:Blue.Cost)(P:Pal ℝ U):
    ply t (affix a P)=affix a (ply t P):=by
  funext e r z
  rw [ply_v]
  simp [affix,Finset.sum_apply,ply_v]
  exact Finset.sum_congr rfl (fun b _=>map_smul t _ _)

theorem grant (P:Era G ℝ)(admit:Auth h P)(a:Blue.Cost):Auth h (affiled a P):=by
  refine ⟨?_,fun n=>affix_shell a _ (admit.span n),fun n=>aspire a _ (admit.pale n),?_⟩
  · intro e r
    change Bends 0 (fun n=>affix a (P.1 n) e r) (affix a P.2 e r)
    simp_rw [affix,Finset.sum_apply]
    exact anzas (P:=fun (b:ℕ×ℕ) n=>coeff b.1 a • P.1 n b.2 r) _ (fun b _=>(admit.wing b.2 r).μ _)
  · intro n t Z I z X Y gate
    change train (spool X) (Blue.flash (ply t (affix a (P.1 n))))=train (spool Y) (Blue.flash (ply t (affix a (P.1 n))))
    rw [natural,sponsor _ a (ply_shell t (admit.span n)),map_mul,map_mul,income,income,(admit.token n t) gate]

theorem read (P:Era G ℝ)(admit:Auth h P)(a:Blue.Cost)(n:Side)(v:TreeVars G n):
    here n v (Blue.flash ((affiled a P).1 n))=a*here n v (Blue.flash (P.1 n)):=by
  change here n v (Blue.flash (affix a (P.1 n)))=_
  rw [sponsor _ _ (admit.span n),map_mul,ground]

theorem risk {n:ℕ}(X:Fin (n+1)→Era G ℝ)(d:Fin (n+1)→ℕ)(entered:∀i,Auth (d i) (X i))
    (C:Fin (n+1)→Blue.Cost):
    MassP G ℝ n (fun i=>affiled (C i) (X i))=affiled (∏i,C i) (MassP G ℝ n X):=by
  apply WilsonIndependentMatchedOpeningFaithful.original
    (manCo _ d (fun i=>grant _ (entered i) _)) (grant _ (manCo X d entered) _)
  intro t y
  rw [WilsonIndependentMatchedOpeningMass.cash _ d (fun i=>grant _ (entered i) _),
    read _ (manCo X d entered),WilsonIndependentMatchedOpeningMass.cash _ d entered]
  simp_rw [read _ (entered _)]
  exact Finset.prod_mul_distrib
end YM.Integration.WilsonIndependentMatchedOpeningFee
