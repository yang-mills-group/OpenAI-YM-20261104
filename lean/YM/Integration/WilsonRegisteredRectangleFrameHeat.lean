import YM.Integration.WilsonRegisteredRectangleFrameRoom
import YM.Integration.WilsonReportingForestAngularCurrency
import YM.Integration.WilsonReportingForestAngularReflection

/-! Uniform physical income on the shared boundary tags of a polynomially growing finite collection of genuine coarse sites. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredRectangleFrameHeat
open Filter Set Finset MeasureTheory Lattice RG Wilson RG16 OPE.Therm
open PhysicalNext.Repeat.Legato WilsonReportingForestPivots WilsonReportingForestAngularFare
open scoped Topology Classical
variable {G:Gauge}(R:Run G)
local notation "A" => R.family.path.levels

def rejected (m per:ℕ)(J:Finset (Site (R.family.side m per))):Set (Config G (R.family.side (m+1) per)):=
  let S:=(A).clock.op m per
  ⋃j:↥J,{U | S.patch.usesMin S.kernel (expandAt (S.ratio.embed j.val) U)}ᶜ

theorem borel (m per:ℕ)(J:Finset (Site (R.family.side m per))):MeasurableSet (rejected R m per J):=by
  apply MeasurableSet.iUnion;intro j;apply MeasurableSet.compl
  let S:=(A).clock.op m per
  apply ((S.patch.min_open (C:=S.kernel) (G:=G)).measurableSet).preimage
  unfold expandAt;fun_prop

theorem purchased (simple:G.Simple)(gate:WilsonReportingForestAngularReflection.posted R)
    (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda (A) m))
    (d h q:ℕ){ε:ℝ}(hp:0<ε):∀ᶠm:ℕ in atTop,∀N,m<N→∀per (J:Finset (Site (R.family.side m per))),
    let b:=(A).clock.hatBeta (m+1)
    (J.card:ℝ) ≤ b^d →
      b^h*(scene R.family.path N per (m+1)).real (rejected R m per J) ≤
        ε*Pert.Asymptotics.regulatorRun R.family N per (m+1)^q:=by
  let D:=d+h+1
  filter_upwards [WilsonRegisteredRectangleFrameRoom.original R simple slow, smaller R simple,
    tag_dates R simple slow,WilsonReportingForestAngularCurrency.currency R simple D q hp,
    WilsonReportingForestAngularReflection.original R simple gate (D+q+1)] with m good little shapes wallet scarce
  intro N live per J b card
  let S:=(A).clock.op m per
  let μ:=scene R.family.path N per (m+1)
  letI:IsProbabilityMeasure μ:=probability R.makes.wilson live
  let τ:=angularCut b
  let α:=(b⁻¹)^(D+q+1)
  have b1:1<b:=(A).fits.delayed _
  have bp:0<b:=zero_lt_one.trans b1
  have ta:0 ≤ τ:=by
    change 0 ≤ (Real.sqrt b)⁻¹*Real.log b*Real.sqrt (Real.sqrt (Real.log b))
    positivity [Real.log_nonneg b1.le]
  have ht:τ ≤ cool (A) (m+1):=little
  have α0:0 ≤ α:=pow_nonneg (inv_nonneg.mpr bp.le) _
  have oneSite (j:↥J):μ.real {U:Config G (R.family.side (m+1) per) |
        S.patch.usesMin S.kernel (expandAt (S.ratio.embed j.val) U)}ᶜ ≤ b*α:=by
    let S₀:=tagCells R m per (S.ratio.embed j.val)
    calc
      _ ≤ μ.real (House.chilly S₀ τ)ᶜ:=by
        apply measureReal_mono
        · intro U hu accepted;exact hu (good per j.val U τ ta ht accepted)
        · exact measure_ne_top μ _
      _ ≤ (S₀.card:ℝ)*α:=House.cool_miss α (scarce N per live) _
      _ ≤ _:=mul_le_mul_of_nonneg_right ((shapes per).2 _) α0
  have total:μ.real (rejected R m per J) ≤ (J.card:ℝ)*(b*α):=calc
    _ ≤ ∑j:↥J,μ.real {U:Config G (R.family.side (m+1) per) |
        S.patch.usesMin S.kernel (expandAt (S.ratio.embed j.val) U)}ᶜ:=measureReal_iUnion_fintype_le _
    _ ≤ ∑_j:↥J,b*α:=sum_le_sum fun j _=>oneSite j
    _ = _:=by simp
  calc
    _ ≤ b^h*(b^d*(b*α)):=mul_le_mul_of_nonneg_left (total.trans (mul_le_mul_of_nonneg_right card (mul_nonneg bp.le α0))) (pow_nonneg bp.le _)
    _ = b^D*α:=by dsimp only [D];rw [pow_succ,pow_add];ring
    _ ≤ _:=wallet N live per

end YM.Integration.WilsonRegisteredRectangleFrameHeat
