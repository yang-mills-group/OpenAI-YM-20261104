import YM.Integration.WilsonIndependentMatchedOpeningComposite
import YM.Integration.WilsonPhysicalMarkedDefectRawCartesian
import YM.Integration.WilsonPositionProgramVisitedTest
/-! Summed thermal prices of the authentic visits of a filed ordinary roster. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOpeningMenu
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
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentMatchedOpeningFiled (terms planted)
open WilsonCoeffUV.StableStrip
open WilsonIndependentMatchedCensusReceipt (Filed)
open WilsonIndependentMatchedFittedSeat (receiving)
open WilsonIndependentMatchedOpeningPorts (Port submitted)
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonIndependentMatchedOpeningRoster (field seat)
open WilsonIndependentMatchedOpeningPayment (affiled)
open RegulatorIR.Cluster
open WilsonIndependentMatchedOpeningCensus (entry pace Sites)
open WilsonIndependentRawRosterWord (degree)
open FVA2 WilsonCoeffUV.Mer.Patrol
open WilsonPhysicalMarkedDefect.RawProduct (belt positive menu)
open WilsonIndependentMatchedOpeningComposite (weight)
def toll (p:ℕ)(a:Blue.Cost):ℝ:=belt p (TaylorWick.into a)
theorem scale (p:ℕ)(b c:ℝ)(a:Blue.Cost):
    toll p (PowerSeries.C b * (a*PowerSeries.C c))=
    toll p a * (|b| * |c|):=by
  unfold toll WilsonPhysicalMarkedDefect.RawProduct.belt TaylorWick.into
  simp only [map_mul,PowerSeries.map_C,PowerSeries.coeff_C_mul,PowerSeries.coeff_mul_C,
    norm_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  have coe (s:ℝ):‖Complex.ofRealHom s‖=|s|:=by change ‖(s:ℂ)‖=|s|;rw [Complex.norm_real,Real.norm_eq_abs]
  rw [coe,coe]
  ring

variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G){d D:ℕ}(w:d<D)
local notation "F" => R.family.labels.level d

def charge (q l:ℕ)(c:Verse F)(φ:Rarity D)(x y M:ℝ):ℝ:=
  ∑b:Alma F,toll q (c b) * (BasePrice l φ x y * (‖jewelBloom w b‖ * M))

theorem one (q l:ℕ)(c:Verse F)(φ:Rarity D)(x y:ℝ)(o:CellR)(M:ℝ)
    (buyer:Amplitude φ M)(xx:0<x)(hx:x≤1):
    (∑z:Port F φ x y o,toll q (PowerSeries.C (drumB l x)*
      realDose R (w:=w) (wheelC x y z.1.val φ.ψ o) c z.2))≤charge R w q l c φ x y M:=by
  unfold charge
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b _
  simp_rw [realDose,scale]
  have due:=WilsonPositionProgramVisitedTest.one (l:=l) φ x y o M buyer xx hx (jewelBloom w b)
  rw [←Finset.sum_coe_sort (VisitsT φ x y o)] at due
  rw [←Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left due (positive q _)

theorem slab {I:Type}[Fintype I](J:I→Type)[∀i,Fintype (J i)](q:ℕ)
    (f:(i:I)→J i→Blue.Cost)(cash:I→ℝ)(earned:∀i,(∑u,toll q (f i u))≤cash i):
    (∑z:((i:I)→J i),toll q (∏i,f i (z i)))≤∏i,cash i:=by
  let g (i:I)(u:J i):=TaylorWick.into (f i u)
  have eqn (z:(i:I)→J i):TaylorWick.into (∏i,f i (z i))=∏i,g i (z i):=map_prod .. 
  have bill (z:(i:I)→J i):toll q (∏i,f i (z i))≤∏i,toll q (f i (z i)):=by
    change WilsonPhysicalMarkedDefect.RawProduct.belt q (TaylorWick.into (∏i,f i (z i)))≤_
    rw [eqn]
    exact WilsonPhysicalMarkedDefect.RawProduct.menu q Finset.univ (fun i=>g i (z i))
  have nonneg (i:I):0≤∑u:J i,toll q (f i u):=Finset.sum_nonneg (fun u _=>positive q (g i u))
  have product:(∏i,∑u:J i,toll q (f i u))≤∏i,cash i:=
    Finset.prod_le_prod (fun i _=>nonneg i) (fun i _=>earned i)
  have swapped:(∏i,∑u:J i,toll q (f i u))=∑z:((i:I)→J i),∏i,toll q (f i (z i)):=
    Fintype.prod_sum _
  exact (Finset.sum_le_sum (fun z _=>bill z)).trans (swapped ▸ product)


theorem original {I:Type}[Fintype I]
    (d D:I→ℕ)(cut:∀i,d i<D i)(c:(i:I)→Verse (R.family.labels.level (d i)))
    (φ:(i:I)→Rarity (D i))(x y:I→ℝ)(o:I→ CellR)(l:I→ℕ)(M:I→ℝ)
    (paid:∀i,Amplitude (φ i) (M i))(pos:∀i,0<x i)(fine:∀i,x i≤1)(q:ℕ):
    let V:=fun i=>Port (R.family.labels.level (d i)) (φ i) (x i) (y i) (o i)
    let fees:((i:I)→V i→Blue.Cost):=fun i z=>PowerSeries.C (drumB (l i) (x i))*
      realDose R (w:=cut i) (wheelC (x i) (y i) z.1.val (φ i).ψ (o i)) (c i) z.2
    (∑z:((i:I)→V i),toll q (∏i,fees i (z i)))≤
      ∏i,charge R (cut i) q (l i) (c i) (φ i) (x i) (y i) (M i):=by
  intro V fees
  exact slab V q fees _ (fun i=>one R (cut i) q (l i) (c i) (φ i) (x i) (y i) (o i) (M i)
    (paid i) (pos i) (fine i))

end YM.Integration.WilsonIndependentMatchedOpeningMenu
