import YM.Integration.FVA1Physical.Wilson.IteratedBankGate
import YM.Integration.FVA1Physical.Wilson.SparseStencil
import YM.Integration.FVA1Physical.Sources.Round2.DistributedFields
import YM.Integration.FVA1Physical.Sources.Round2.PosteriorReclock

/-! Construct the distributed incoming Wilson source from all physical
insertion slots, before choosing the gauge forest of the next block. The
coefficients are the fixed local Taylor derivatives of the genuine mixed field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Set Finset Lattice RG YM.Wilson Tree Precision Exterior Push.Uniform
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open MSbar MSbar.Whisk MSbar.Bout MSbar.Cacao MSbar.Lis MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal MSbar.Mosaic MSbar.Wave
open YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical BigOperators Topology
variable {G:Gauge} {I:Type} [Fintype I] (J:I→Lamp G)

def inletSlot {n:Side} (o:I→Site n) (w:Wire G ↥(Finset.univ : Finset (Slice J))) : Primary n G :=
  (((legs J o w.1.val).1,Exterior.coord (legs J o w.1.val).2),w.2)

def stencilInlet {n:Side} (o:I→Site n) (part:Bool):Nesting G n :=
  PowerSeries.mk fun i=>MvPolynomial.rename (inletSlot J o) (lampRow J part Finset.univ i)

theorem inlet_reading {n:Side} (o:I→Site n) (g:ℝ) (part:Bool) (p:ℕ) (U:Config G n):
    clockReading p g (stencilInlet J o part) (chartLog g U) = sparseTaylor J o g part p U:=by
  unfold clockReading taste picture sparseTaylor
  apply Finset.sum_congr rfl;intro i _
  rw [PowerSeries.coeff_map,stencilInlet,PowerSeries.coeff_mk,MvPolynomial.eval_rename]
  apply congrArg (fun v=>g^i*MvPolynomial.eval v (lampRow J part Finset.univ i))
  funext w
  let e:=legs J o w.1.val
  change g⁻¹*(logWithin G (U (e.1,axisEquiv.symm (Exterior.coord e.2)))) w.2 = g⁻¹*(logWithin G (U e)) w.2
  rw [show axisEquiv.symm (Exterior.coord e.2)=e.2 from axisEquiv.symm_apply_apply _]

theorem inlet_degree {n:Side} (o:I→Site n) (part:Bool) (i:ℕ):
    (PowerSeries.coeff i (stencilInlet J o part)).totalDegree ≤ i:=by
  rw [stencilInlet,PowerSeries.coeff_mk]
  exact (MvPolynomial.totalDegree_rename_le ..).trans (lampRow_degree J part Finset.univ i)

theorem inlet_bank (p s m L:ℕ) (part:Bool) (pm:p ≤ m) {δ:ℝ} (δp:0 < δ):
    ∀ᶠ y:ℝ in atTop,∀ (n:Side) (o:I→Site n) (b:Site n),
      (∀ j:Slice J,separation b (legs J o j).1 ≤ L*closeN y) →
      BankPaid b y s p m δ (stencilInlet J o part):=by
  have rise:Tendsto (fun y:ℝ=>y) atTop atTop:=tendsto_id
  let weight:=fun y:ℝ=>liftW (αm y) s (L*closeN y)
  have rate:Mosaic.Run atTop (fun y:ℝ=>y) weight 0:=by
    simpa only [one_mul] using (Mosaic.Issue.nearB rise 1 zero_lt_one s L).2
  choose B e _ native using fun i:Fin (p+1)=>fixed_polynomial_vault (lampRow J part Finset.univ i.val) m
  have scheduled (i:Fin (p+1)):∀ᶠ y:ℝ in atTop,B i*(weight y)^(e i) ≤ y^δ:=by
    have h:=(rate.Ypow rise (e i)).mulK rise (B i)
    filter_upwards [h δ δp] with y bound
    exact (le_abs_self _).trans bound
  filter_upwards [eventually_all.mpr scheduled] with y pay n o b near t ht
  let i:Fin (p+1):=⟨t,by omega⟩
  have a0:0 ≤ αm y:=by unfold αm hatW Alto.flurry;positivity
  have nr (w:Wire G ↥(Finset.univ : Finset (Slice J))) :
      liftW (αm y) s (separation b (Measuring.chart n G (inletSlot J o w))) ≤ weight y:=
    w_more (near w.1.val) a0 _
  refine ⟨(inlet_degree J o part t).trans (ht.trans pm),?_⟩
  rw [stencilInlet,PowerSeries.coeff_mk]
  exact Quote.widen (native i (Measuring.chart n G) b (inletSlot J o) s (αm y) (weight y) a0
    (w_start a0 s _) nr) (pay i) le_rfl

end YM.Integration.FVA1Physical.Wilson
