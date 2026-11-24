import YM.Integration.WilsonOrdinaryNestedFixedInput

/-! The independent tested OPE is the smear of the very same finite
pointwise OPE, with its inverse output conversion and every retained axis. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOrdinaryNestedTestedMS
open Function Set Filter MeasureTheory Spec RG17 Maxwell MS MS.Local.Physical MS.Fleet MS.Land MS.Menus
open MS.Theater FVA2 FVA2.Scale FVA2.Register XSpace Pert Pert.Position PowerSeries
open XSpace.Normalize FVA2.O FVA2.O.Score FVA2.O.Project MS.High MS.Wind MS.Native MS.Tide
open WilsonMSDictionaryVector WilsonMSDictionaryFarRead WilsonOrdinaryNestedBasis
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} (R:PhysicalNext.Repeat.Legato.Run G) (Z:WilsonPrescription G)
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
    {simple:G.Simple} {σ:Prescription (Press.portDeck G)} {dial:Bool} (ms:Main.Match Z simple M σ dial)
    {n:ℕ} (d:Fin n→ℕ)
local notation "W" => Measure.outlook Z.scheme Z.criterion

include ms ν in
theorem coefficient (u:Scan G n)(b:Q G) (q:ℕ) (g:ℝ) :
    ContinuousOn (fun x=>cutoff q g ((Canon.FarCoefficients W u) x b)) (conf n):=by
  apply continuousOn_finsetSum
  intro j _
  exact continuousOn_const.mul (((ms.separatedOPE ν).wilson.far u).2.1 b j)

include ms ν in
theorem scalar (ψ:Test n) (u:Scan G n)(b:Q G) (q:ℕ)(g:ℝ):
    ψ.applyTo (fun x=>cutoff q g ((Canon.FarCoefficients W u) x b)) =
      cutoff q g (Canon.Yield ψ (Canon.FarCoefficients W u) b):=by
  have cx (j:ℕ) (x:Points n) (hx:x∈tsupport ψ) :
      ContinuousAt (fun y=>coeff j ((Canon.FarCoefficients W u) y b)) x:=
    ((((ms.separatedOPE ν).wilson.far u).2.1 b j) x (ψ.tsupport_subset hx)).continuousAt
      ((conf_open n).mem_nhds (ψ.tsupport_subset hx))
  have wage (j:ℕ):Integrable (fun x:Points n=>ψ x * coeff j (Canon.FarCoefficients W u x b)) :=
    RG17.localized ψ _ (cx j)
  unfold Test.applyTo cutoff
  simp only [Finset.mul_sum,Canon.Yield,Read.smearing,coeff_mk,Test.applyTo]
  simp_rw [mul_left_comm (ψ _)]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro j _
    exact (wage j).const_mul _

include ms ν in
theorem point (h q:ℕ)(g:ℝ)(c:Choice G d) :
    ContinuousOn (fun z=>WilsonOrdinaryNestedMSPoint.field Z M ν R.family d h
      (axes (R:=R) d c) z q g) (conf n):=by
  simp_rw [WilsonOrdinaryNestedMSPoint.issued Z M ν ms, on_axis]
  apply continuousOn_finsetSum
  intro b _
  exact (coefficient Z M ν ms _ _ q g).smul continuousOn_const

include ms ν in
theorem filed (ψ:Test n) (h q:ℕ)(g:ℝ)(c:Choice G d) :
    (∫z:Points n,ψ z • WilsonOrdinaryNestedMSPoint.field Z M ν R.family d h (axes (R:=R) d c) z q g) =
      prediction R.family d h Z M ν (axes (R:=R) d c) ψ q g:=by
  let u:Scan G n:=fun i=>Dframe.flash (c i)
  let a(b:Dframe.Toon G h)(z:Points n):=cutoff q g (Canon.FarCoefficients W u z (Dframe.flash b))
  let v(b:Dframe.Toon G h):=WilsonMSDictionaryVector.basis R.family h b
  have localCont (b:Dframe.Toon G h) (z:Points n)(hz:z∈tsupport ψ):ContinuousAt (a b) z:=
    (coefficient Z M ν ms u _ q g z (ψ.tsupport_subset hz)).continuousAt
      ((conf_open n).mem_nhds (ψ.tsupport_subset hz))
  have payout (b:Dframe.Toon G h):Integrable (fun z:Points n=>ψ z * a b z):=
    RG17.localized ψ _ (localCont b)
  simp_rw [WilsonOrdinaryNestedMSPoint.issued Z M ν ms,on_axis,Finset.smul_sum,smul_smul]
  unfold prediction
  rw [on_axis]
  simp_rw [WilsonMSDictionaryFarRead.converted_eq Z M ν ms]
  change (∫z:Points n,∑b,(ψ z*a b z) • v b) =
    ∑b,cutoff q g (Canon.Yield ψ (Canon.FarCoefficients W u) (Dframe.flash b)) • v b
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro b _
    rw [integral_smul_const]
    exact congrArg (fun A:ℂ=>A • v b) (scalar Z M ν ms ψ u (Dframe.flash b) q g)
  · intro b _
    exact (payout b).smul_const _
end YM.Integration.WilsonOrdinaryNestedTestedMS
end
