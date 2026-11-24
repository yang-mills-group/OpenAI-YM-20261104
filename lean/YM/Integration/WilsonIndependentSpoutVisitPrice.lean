import YM.Integration.WilsonIndependentMatchedOpeningMenu

/-! A single product of native profile and coefficient prices controls the thermal charge of all physical visits. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutVisitPrice
open Finset PowerSeries Function Lattice RG Source Labels Precision WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos WilsonCoeffUV.Power WilsonCoeffUV.Wheel.Flooring
open WilsonIndependentMatchedOpeningMenu (toll charge)
open WilsonIndependentMatchedOpeningPorts (Port)
open WilsonIndependentMatchedTopReceipt (realDose)
open FVA2 RegulatorIR
open scoped BigOperators Classical
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)
theorem thermal (q:ℕ)(c:Blue.Cost):(∑j:Fin (q+1),‖coeff j.val c‖)=toll q c:=by
  unfold WilsonIndependentMatchedOpeningMenu.toll WilsonPhysicalMarkedDefect.RawProduct.belt TaylorWick.into
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [PowerSeries.coeff_map]
  exact (Complex.norm_real _).symm

theorem original {I:Type}[Fintype I](d D:I→ℕ)(cut:∀i,d i<D i)(c:(i:I)→Verse (R.family.labels.level (d i)))
    (φ:(i:I)→Rarity (D i))(x y:I→ℝ)(o:I→CellR)(l:I→ℕ)(M:I→ℝ)
    (paid:∀i,Amplitude (φ i) (M i))(pos:∀i,0<x i)(fine:∀i,x i≤1)(q:ℕ):
    let V:=fun i=>Port (R.family.labels.level (d i)) (φ i) (x i) (y i) (o i)
    let fees:((i:I)→V i→Blue.Cost):=fun i z=>PowerSeries.C (drumB (l i) (x i))*
      realDose R (w:=cut i) (wheelC (x i) (y i) z.1.val (φ i).ψ (o i)) (c i) z.2
    (∑j:((i:I)→V i) × Fin (q+1),‖PowerSeries.coeff j.2.val (∏i,fees i (j.1 i))‖)≤
      ∏i,charge R (cut i) q (l i) (c i) (φ i) (x i) (y i) (M i):=by
  intro V fees
  rw [Fintype.sum_prod_type]
  simp_rw [thermal]
  exact WilsonIndependentMatchedOpeningMenu.original R d D cut c φ x y o l M paid pos fine q

end YM.Integration.WilsonIndependentSpoutVisitPrice
