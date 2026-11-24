import YM.Integration.WilsonCoherentMayerPriorJet
import YM.Integration.SignedMarkedRayFloor
import YM.Integration.SignedFormalPowerLayers
import YM.Comparison.RG02.Thermal.Kept

/-! The coefficients of the paid physical mask on an actual signed and normalized finite extension. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorCoefficient
open Function Filter Finset Lattice Wilson RG Marker Multi Exterior Precision LocalComparison
open Comparison.RG02 Comparison.RG02.Assembly Comparison.RG02.Valence NativePaidPacketColors
open WilsonMeasuredPathTaylor WilsonCoherentMayerPriorDifferential Comparison.Density.RenderM Next.SectorChange.Flat
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {S:Census V}
variable {D : V → ComparisonDensity.Address.Orbit} {n : Side} (P : MarkedPackets D G n S)

def stratum (x:TestSpace D)(s:S.Mode)(z:ℤ)(A:fieldDir G n 1):ℂ:=
  NativePaidPacketSeries.value P s z x (represent A)

def layer (x:TestSpace D)(s:S.Mode)(k:ℕ)(z:ℤ)(B:fieldDir G n 1):ℂ:=
  if z≤(k:ℤ) then Assembly.jet (stratum P x s z) ((k:ℤ)-z).toNat B else 0

variable {P} {p:BudgetPoint} {ad:V→Support n} {reg:Comparison.Density.Testing.Region (fun i=>(D i).Mood) n}
    {w:V→ℝ} {g width bill:ℝ} {off slope:ℕ} (H:P.Paid p ad reg w g width bill off slope) (hg:g≠0)

private theorem jet_sum {E I:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s:Finset I) (f:I → E → ℂ)
    (h:∀i∈s,ContDiffAt ℝ ω (f i) 0) (k:ℕ) (u:E):
    Assembly.jet (fun a=>∑i∈s,f i a) k u=∑i∈s,Assembly.jet (f i) k u := by
  unfold Assembly.jet
  rw [iteratedFDeriv_fun_sum_apply (fun i hi=>(h i hi).of_le le_top)]
  simp [smul_sum]

include H hg in
theorem filed (x:TestSpace D)(s:S.Mode)(hs:s≠S.quiet)(k:ℕ)(B:fieldDir G n 1)
    (E:ℝ→fieldDir G n 1→Poly S)
    (value:∀t:ℝ,t≠0→∀A,E t A=P.read x t (represent (t•A)))
    (live:∀A,ContinuousAt (fun t=>E t A) 0)(smooth:ContDiffAt ℝ k (fun t=>E t B) 0):
    (((k.factorial:ℝ)⁻¹) • iteratedFDeriv ℝ k (fun t:ℝ=>E t B) 0 (fun _=>1):Poly S).part s=
      ∑z∈powers P,layer P x s k z B:=by
  have regular (z:ℤ):ContDiffAt ℝ ω (stratum P x s z) 0:=(NativePaidPacketSeries.value_grade H hg s hs z x).smooth
  let π : Poly S →L[ℝ] ℂ := ContinuousLinearMap.proj s
  let L : ℝ×(fieldDir G n 1) →L[ℝ] (fieldDir G n 1) := ContinuousLinearMap.snd ℝ ℝ (fieldDir G n 1)
  let f (z:ℤ) := stratum P x s z ∘ L
  let e (z:ℤ) := ((P.powerCap:ℤ)+z).toNat
  let a (z:ℤ) (u:ℝ×(fieldDir G n 1)) := u.1^(e z) • f z u
  have hf (z:ℤ) : ContDiffAt ℝ ω (f z) 0 := by
    apply ContDiffAt.comp (0:ℝ×(fieldDir G n 1)) _ L.contDiff.contDiffAt
    simpa only [L.map_zero] using regular z
  have ha (z:ℤ) : ContDiffAt ℝ ω (a z) 0 := (contDiffAt_fst.pow (e z)).smul (hf z)
  have hn : SignedMarkedRayFloor.numerator P x s=fun u=>∑z∈powers P,a z u := by
    funext u;simp only [SignedMarkedRayFloor.numerator,if_neg hs];rfl
  calc _=Assembly.jet (π ∘ fun t=>E t B) k 1:=Assembly.jet_apply_left π _ k smooth 1
       _=Assembly.jet (SignedMarkedRayFloor.numerator P x s) (P.powerCap+k) (1,B):=SignedMarkedRayFloor.ray H hg x s E value live k B
       _=∑z∈powers P,Assembly.jet (a z) (P.powerCap+k) (1,B):=by rw [hn,jet_sum _ a (fun z _=>ha z)]
       _=_:=by
         apply sum_congr rfl;intro z hz
         have lo:-(P.powerCap:ℤ)≤z:=(mem_Icc.mp hz).1
         have he:((e z:ℕ):ℤ)=(P.powerCap:ℤ)+z:=by unfold e;omega
         change Assembly.jet (fun u:ℝ×(fieldDir G n 1)=>u.1^(e z) • f z u) _ (1,B)=_
         rw [SignedFormalPowerLayers.shifted (hf z) _ _ _ rfl]
         by_cases hzk:z≤(k:ℤ)
         · rw [if_pos (by omega: e z≤P.powerCap+k),layer,if_pos hzk,show P.powerCap+k-e z=((k:ℤ)-z).toNat by omega]
           exact Assembly.jet_continuous_right L ((regular z).of_le le_top) (1,B)
         rw [if_neg (by omega : ¬e z≤P.powerCap+k),layer,if_neg hzk]


include H hg in
omit [Fintype V] in
theorem radial (x:TestSpace D)(s:S.Mode)(hs:s≠S.quiet)(z:ℤ)(a:Directions G n)(k:ℕ):
    ((k.factorial:ℝ)⁻¹) • iteratedDeriv k (reading P s z x a) 0=
      Assembly.jet (stratum P x s z) k (labels a):=by
  let L:ℝ→L[ℝ](fieldDir G n 1):=ContinuousLinearMap.toSpanSingleton ℝ (labels a)
  have eq:reading P s z x a=stratum P x s z ∘ L:=by
    funext t
    change NativePaidPacketSeries.value P s z x (field a t)=NativePaidPacketSeries.value P s z x (represent (t•labels a))
    rw [represent_field]
  rw [eq,iteratedDeriv_eq_iteratedFDeriv]
  change Assembly.jet (stratum P x s z ∘ L) k 1=_
  calc
    _=Assembly.jet (stratum P x s z) k (L 1):=Assembly.jet_continuous_right L
      (show ContDiffAt ℝ k (stratum P x s z) 0 from (NativePaidPacketSeries.value_grade H hg s hs z x).smooth.of_le le_top) 1
    _=_:=congrArg _ (one_smul ℝ (labels a))

end YM.Integration.WilsonCoherentMayerPriorCoefficient
