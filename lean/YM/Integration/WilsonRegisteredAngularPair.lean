import YM.Integration.WilsonHeldEventMass
import YM.Integration.WilsonRegisteredSoftCovariance
import YM.Integration.WilsonReportingForestAngularCurrency
import YM.Integration.WilsonReportingForestAngularReflection

/-! The angular rejection for two actual registered insertions. Both
conditional means may depend on the same lower gauge field. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonRegisteredAngularPair
open Function Filter Set MeasureTheory Lattice Wilson RG OPE.Therm PhysicalNext.Repeat.Legato
open RG16 RG05Readout Address Native Pulse MSbar.Heath Precision PertExtension
open WilsonLimitConstruction Pert.Asymptotics WilsonReportingForestPivots WilsonInheritedRegisteredField
open WilsonReportingForestAngularFare WilsonReportingForestAngularReflection
open scoped Classical Topology
variable {G : Gauge} (R : Run G) {N m per : ℕ}

def center (use:Bool) (f:Config G (R.family.side (m+1) per)→ℝ) (V:Config G (R.family.side m per)) : ℝ :=
  if use then actualAverage R.family (N:=N) f V else 0

private theorem centered (live:m<N) (use:Bool) (f:Config G (R.family.side (m+1) per)→ℝ)
    {a:ℝ} (bound:∀U,|f U|≤a) (V:Config G (R.family.side m per)) (U:Config G (R.family.side (m+1) per)) :
    |f U-center R (N:=N) use f V|≤2*a := by
  have absolute : ∀W,‖f W‖≤a := by simpa only [Real.norm_eq_abs] using bound
  have mean : |center R (N:=N) use f V|≤a := by
    cases use with
    | false => simpa [center] using (abs_nonneg (f U)).trans (bound U)
    | true =>
      simpa only [center,ite_true,Real.norm_eq_abs] using actualAverage_norm_le R.family R.makes live absolute V
  have sub : |f U-center R (N:=N) use f V| ≤ |f U|+|center R (N:=N) use f V| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le (f U) (center R (N:=N) use f V)
  exact sub.trans ((add_le_add (bound U) mean).trans_eq (by ring))

variable (simple : G.Simple) {ρ : ℝ} {T : Campaign R} {P : Campaign.Pillars R T}
    (funded : FundedOriginalProperties.{u} simple ρ P)
local notation "β" => R.family.path.levels.clock.hatBeta

include simple funded in
theorem original (gate:posted R) (slow:∀j,((R.family.S.block j).val:ℝ)≤Real.log (RG16.Lambda R.family.path.levels j))
    (ev ew q:ℕ) {ε:ℝ} (he:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀ N per (live:m<N) (dv dw:ℕ) (_rv:R.family.ref dv ≤ m+1) (_rw:R.family.ref dw ≤ m+1)
      (v:R.family.label dv) (w:R.family.label dw) (o:Fin 2→Site (R.family.side (m+1) per)) (Mv Mw:ℝ),
      0≤Mv → 0≤Mw →
      Next.UVStress.quota R.family dv (m+1) N per v≤R.family.S.a (m+1)^dv*(β (m+1)^ev*Mv) →
      Next.UVStress.quota R.family dw (m+1) N per w≤R.family.S.a (m+1)^dw*(β (m+1)^ew*Mw) →
      ∀ (η χ:ℂ→L[ℝ]ℝ) (firstMean secondMean:Bool),
      let k:=m+1
      let D:=⋃i,(House.chilly (G:=G) (tagCells R m per (o i)) (angularCut (β k)))ᶜ
      let f:=fun U=>η (regular R.makes live v (o 0) U)
      let h:=fun U=>χ (regular R.makes live w (o 1) U)
      let read:=actualAverage R.family (N:=N) (p:=per) (m:=m) (E:=ℝ)
      (∫V,‖read (D.indicator (fun U=>(f U-center R (N:=N) firstMean f V)*
            (h U-center R (N:=N) secondMean h V))) V‖ ∂scene R.family.path N per m) ≤
        ε*regulatorRun R.family N per k^q*(‖η‖*‖χ‖)*(Mv*Mw) := by
  let d:=(ev+1)+(ew+1)
  let l:=ε/36
  have pos : 0<l:=div_pos he (by norm_num)
  let τ (j:ℕ):=angularCut (β (j+1))
  have rare:=WilsonReportingForestAngularReflection.original R simple gate (d+1+q+1)
  have sell:=WilsonReportingForestAngularCurrency.tested (I:=Fin 2) R simple slow τ d q pos rare
  filter_upwards [sell] with m acquired
  intro N per live dv dw rv rw v w o Mv Mw pv pw cv cw η χ leftMean rightMean k D f h read
  let E:=‖η‖*‖χ‖*(Mv*Mw)
  have epos : 0≤E := by positivity
  have bu : 0≤β k:=zero_le_one.trans (R.family.path.levels.fits.delayed k).le
  have supf (U) : |f U|≤‖η‖*(3*(β k)^(ev+1)*Mv) :=
    (η.le_opNorm _).trans (mul_le_mul_of_nonneg_left (WilsonRegisteredSoftCovariance.gross R simple funded
      live rv v (o 0) U ev pv cv) (norm_nonneg _))
  have suph (U) : |h U|≤‖χ‖*(3*(β k)^(ew+1)*Mw) :=
    (χ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (WilsonRegisteredSoftCovariance.gross R simple funded
      live rw w (o 1) U ew pw cw) (norm_nonneg _))
  let X:=fun V U=>(f U-center R (N:=N) leftMean f V)*(h U-center R (N:=N) rightMean h V)
  have cap (V U) : |X V U|≤36*E*(β k)^d := by
    change |(_ : ℝ)*_|≤_
    rw [abs_mul]
    calc
      _ ≤ (2*(‖η‖*(3*(β k)^(ev+1)*Mv)))*(2*(‖χ‖*(3*(β k)^(ew+1)*Mw))) :=
        mul_le_mul (centered R live leftMean f supf V U) (centered R live rightMean h suph V U) (abs_nonneg _) (by positivity)
      _ = _ := by dsimp only [d,E];rw [pow_add];ring
  have md:MeasurableSet D:=MeasurableSet.iUnion fun _=>(House.bath (G:=G) _).compl
  have use:=WilsonHeldEventMass.original R live md X (36*E*(β k)^d) (by positivity) (fun V U _=>cap V U)
  have budget:= (acquired N live per o).1
  change (β k)^d*(scene R.family.path N per k).real D≤l*regulatorRun R.family N per k^q at budget
  have final : 36*l=ε := by dsimp only [l];ring
  calc
    _ ≤ _ := use
    _ = (36*E)*((β k)^d*(scene R.family.path N per k).real D) := by ring
    _ ≤ (36*E)*(l*regulatorRun R.family N per k^q) := mul_le_mul_of_nonneg_left budget (by positivity)
    _ = _ := by dsimp only [E];rw [←final];ring

end YM.Integration.WilsonRegisteredAngularPair
end
