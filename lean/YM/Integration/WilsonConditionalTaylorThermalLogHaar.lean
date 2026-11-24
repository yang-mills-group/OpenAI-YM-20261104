import YM.Integration.WilsonConditionalTaylorThermalFourthActivity

/-! The logarithmic quadratic angular Haar vertex is a single sum over
the actual finite links, after canceling all pairs of distinct links. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalLogHaar
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested Radial
open WilsonConditionalTaylorThermalLaplace WilsonConditionalTaylorThermalInteraction WilsonConditionalTaylorThermalFourthActivity
open scoped Classical BigOperators ContDiff Topology

def logarithmic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E→ℝ) (x : E) :=
  jet F 2 x/F 0 - (jet F 1 x/F 0)^2/2

theorem born {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (x : E) :
    logarithmic (fun _ : E=>c) x=0 := by
  simp [logarithmic,jet,iteratedFDeriv_const_of_ne (show 2≠0 by decide),
    iteratedFDeriv_const_of_ne (show 1≠0 by decide)]

theorem product {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {F J : E→ℝ}
    (sf : ContDiffAt ℝ ∞ F 0) (sj : ContDiffAt ℝ ∞ J 0) (f : F 0≠0) (j : J 0≠0) (x : E) :
    logarithmic (F*J) x=logarithmic F x+logarithmic J x := by
  have vF : RadialOrder 0 F := fun y=>(directions sf y).bounded
  have vJ : RadialOrder 0 J := fun y=>(directions sj y).bounded
  have one := WilsonConditionalTaylorThermalNextProduct.jets sf sj vF vJ x
  have two := WilsonConditionalTaylorThermalSecondProduct.jets sf sj vF vJ x
  simp only [Nat.zero_add,jet_zero] at one two
  unfold logarithmic;rw [one,two]
  simp only [Pi.mul_apply]
  field_simp [f,j];ring

variable {G : Gauge} {n c : Side} {d : Descent n c}
local notation "E" => Coordinates G d
def leaf (P : ChartRatio G) (i : d.Links) (x : E) := Chart.fee P (x i)

theorem bonds (P : ChartRatio G) (R : LocalRatio P) (x : E) :
    logarithmic (haar P d) x=∑ i : d.Links,logarithmic (leaf P i) x := by
  have good (i : d.Links) : ContDiffAt ℝ ∞ (leaf P i) 0 := by
    have single : ContDiffAt ℝ ∞ (Chart.fee P) ((0:E) i) := (Chart.Ratio.fee_smooth R).of_le (by simp)
    exact single.comp (f:=fun y : E=>y i) 0 (contDiffAt_apply ℝ G.Color _ _)
  have pos (i : d.Links) : 0<leaf P i 0 :=
    lt_max_of_lt_left (by change 0<P.scale*P.J 0;rw [R.anchored,mul_one];exact R.scale)
  let tissue (s : Finset d.Links) : E→ℝ := ∏ i∈s,leaf P i
  have tissue0 (s : Finset d.Links) : 0<tissue s 0 := by
    simp only [tissue,Finset.prod_apply];exact Finset.prod_pos fun i _=>pos i
  have smooth (s : Finset d.Links) : ContDiffAt ℝ ∞ (tissue s) 0 := by
    change ContDiffAt ℝ ∞ (∏i∈s,leaf P i) 0
    first | exact contDiffAt_prod (fun i _=>good i) | exact contDiffAt_prod' (fun i _=>good i)
  have survey (s : Finset d.Links) : logarithmic (tissue s) x=∑i∈s,logarithmic (leaf P i) x := by
    induction s using Finset.induction_on with
    | empty => simp only [tissue,Finset.prod_empty,Finset.sum_empty];exact born 1 x
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi,show tissue (insert i s)=leaf P i*tissue s from Finset.prod_insert hi,
        product (good i) (smooth s) (pos i).ne' (tissue0 s).ne',ih]
  let K : ℝ := (Fintype.card d.Tags:ℝ)⁻¹
  have kn : K≠0 := inv_ne_zero (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero))
  have enter : haar P d=tissue Finset.univ*(fun _ : E=>K) := by
    funext y;simp [haar,tissue,leaf,Chart.jacobian,K]
  rw [enter,product (smooth _) contDiffAt_const (tissue0 _).ne' kn,born,add_zero,survey]

theorem official (P : ChartRatio G) (R : LocalRatio P) (t : d.Tags) (x : E) :
    second P t x = (interaction P t x)^2/2+
      ((∑i:d.Links,logarithmic (leaf P i) x)-jet (d.phase G t) 4 x) := by
  rw [←bonds P R]
  change _ = _+(jet (haar P d) 2 x/density d P-(jet (haar P d) 1 x/density d P)^2/2-_)
  unfold second interaction
  ring

end YM.Integration.WilsonConditionalTaylorThermalLogHaar
