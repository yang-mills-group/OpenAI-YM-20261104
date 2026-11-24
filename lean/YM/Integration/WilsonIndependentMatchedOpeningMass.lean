import YM.Integration.WilsonIndependentMatchedOpeningFaithful
import YM.Integration.WilsonIndependentMatchedOpeningPayment
import YM.Integration.WilsonIndependentMatchedTotalTop
/-! Expand the true loaded ordinary product in its finite port stencils before a common old vacuum acts. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOpeningMass
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
open WilsonCoeffUV.Mer
variable {G:Gauge}{n:ℕ}
theorem cash (X:Fin (n+1)→Era G ℝ)(d:Fin (n+1)→ℕ)(paid:∀i,Auth (d i) (X i))
    (t:Side)(v:TreeVars G t):
    here t v (Blue.flash ((MassP G ℝ n X).1 t))=∏i,here t v (Blue.flash ((X i).1 t)):=by
  induction n with
  | zero=>simp [MassP]
  | succ n ih=>
    conv_rhs => rw [Fin.prod_univ_succ]
    have hi:=manCo (Fin.tail X) (Fin.tail d) (fun j=>paid j.succ)
    change here t v (Blue.flash (woad _ _))=_
    rw [woadap _ _ (finite_shell ((paid 0).span t)) (finite_shell (hi.span t)),map_mul,
      ih (Fin.tail X) (Fin.tail d) (fun j=>paid j.succ)]
    rfl

theorem sum (J:Type)[Fintype J](X:J→Era G ℝ)(d:ℕ)(paid:∀i,Auth d (X i))
    (t:Side)(v:TreeVars G t):
    here t v (Blue.flash ((∑i,X i).1 t))=∑i,here t v (Blue.flash ((X i).1 t)):=by
  have fields:(∑i,X i).1 t=∑i,(X i).1 t:=by simp only [Prod.fst_sum,Finset.sum_apply]
  rw [fields,flash_term _ (fun i _=>(paid i).span t),map_sum]

theorem original (J:Fin (n+1)→Type)[∀i,Fintype (J i)](d:Fin (n+1)→ℕ)
    (X:(i:Fin (n+1))→J i→Era G ℝ)(paid:∀i j,Auth (d i) (X i j)):
    MassP G ℝ n (fun i=>∑j,X i j)=∑z:((i:Fin (n+1))→J i),MassP G ℝ n (fun i=>X i (z i)):=by
  let h:=∑i,d i
  have a (i):Auth (d i) (∑j,X i j):=Auth.sum (fun j _=>paid i j)
  have b (z:(i:Fin (n+1))→J i):Auth h (MassP G ℝ n (fun i=>X i (z i))):=manCo _ d (fun i=>paid i (z i))
  apply WilsonIndependentMatchedOpeningFaithful.original (manCo _ d a) (Auth.sum (fun z _=>b z))
  intro t v
  rw [cash _ d a,sum _ _ h b]
  simp_rw [sum _ _ _ (paid _),cash _ d (fun i=>paid i _)]
  exact Fintype.prod_sum _

end YM.Integration.WilsonIndependentMatchedOpeningMass
