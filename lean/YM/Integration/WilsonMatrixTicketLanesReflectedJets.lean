import YM.Integration.WilsonMatrixTicketLanesReflectedGauge

/-! Exact degree and first coefficient of finite words in the gauge-fixed true compact link angles. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReflectedJets
open Function Filter MeasureTheory PowerSeries Gauge
open PertExtension PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice
open RGComparison.Core16 RGComparison.Core16.Lumen RGComparison.Core16.Lumen.Planet
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {I K : Type} [Fintype I] [NormedAddCommGroup K] [NormedSpace ℝ K]
    [FiniteDimensional ℝ K]
local notation "V" => Fk.Panel G I × K

def site (i : Wire G I) : V→L[ℝ] G.Color :=
  (ContinuousLinearMap.proj i.1) ∘L ContinuousLinearMap.fst ℝ _ _

def source (i : Wire G I) (z : V) : ℝ := (Lumen.turn ((site i) z)) i.2

def deposited (w : Rail G I) (z : V) : ℝ := (w.map fun i=>source i z).prod

def later (i : Wire G I) : Ticket V := Stack.drop 1 (Stack.rise (source i))

def entries (w : Rail G I) : Ticket V := (w.map fun i=>later i).prod

omit [FiniteDimensional ℝ K] in
private theorem analytic (i : Wire G I) : ContDiff ℝ ω (source (K:=K) i) :=
  (EuclideanSpace.proj i.2:G.Color→L[ℝ] ℝ).contDiff.comp (Lumen.turn_hot.comp (site (K:=K) i).contDiff)

omit [FiniteDimensional ℝ K] in
private theorem smooth (w : Rail G I) : ContDiff ℝ ω (deposited (K:=K) w) := by
  induction w with
  | nil => exact contDiff_const
  | cons i w ih => exact (analytic i).mul ih

private theorem one (i : Wire G I) : Stack.rise (source (K:=K) i) = X*later i := by
  apply PowerSeries.ext;intro l
  cases l with
  | zero =>
    simp only [coeff_zero_eq_constantCoeff_apply,map_mul,constantCoeff_X,zero_mul]
    rw [←coeff_zero_eq_constantCoeff_apply,Stack.rise,coeff_mk]
    apply Subtype.ext;funext x
    change jet (source (K:=K) i) 0 x=0
    simp [jet_zero,source,map_zero,turn_zero]
  | succ n => simp [later,Stack.drop,coeff_succ_X_mul,Nat.add_comm]

private theorem first (i : Wire G I) (x : V) : (constantCoeff (later i)).val x=x.1 i.1 i.2 := by
  have ts : HasFDerivAt (turn (G:=G)) (ContinuousLinearEquiv.refl ℝ G.Color).toContinuousLinearMap (site (K:=K) i 0) := by
    rw [map_zero];exact Lumen.turn_roll
  have h := (EuclideanSpace.proj i.2:G.Color→L[ℝ] ℝ).hasFDerivAt.comp (0:V) (ts.comp 0 (site (K:=K) i).hasFDerivAt)
  rw [←coeff_zero_eq_constantCoeff_apply,later,Stack.drop,coeff_mk,Nat.add_zero,Stack.rise,coeff_mk]
  change jet (source (K:=K) i) 1 x = x.1 i.1 i.2
  rw [Radial.jet,iteratedFDeriv_one_apply,show fderiv ℝ (source (K:=K) i) 0 = _ from h.fderiv]
  simp [site]

/-- No Taylor coefficient of the true angular word before its number of letters survives. -/
theorem expansion (w : Rail G I) : Stack.rise (deposited (K:=K) w)=X^w.length*entries w := by
  induction w with
  | nil => change Stack.rise (1:V→ℝ)=X^0*1;rw [Stack.rise_one,pow_zero,one_mul]
  | cons i w ih =>
    change Stack.rise (source (K:=K) i*deposited w)=X^(w.length+1)*(later i*entries w)
    rw [Stack.rise_mul (analytic i|>.contDiffAt.of_le le_top) (smooth w|>.contDiffAt.of_le le_top),one,ih,pow_succ];ring

/-- Its exact initial coefficient evaluates to the unmodified real tangent charges on all free links. -/
theorem base (w : Rail G I) (x : V) : (constantCoeff (entries w)).val x=(w.map fun i=>x.1 i.1 i.2).prod := by
  induction w with
  | nil => change (constantCoeff (1:Ticket V)).val x=1;rw [map_one];rfl
  | cons i w ih =>
    change (constantCoeff (later i*entries w)).val x=x.1 i.1 i.2*(w.map fun t=>x.1 t.1 t.2).prod
    rw [map_mul];change (constantCoeff (later i)).val x*(constantCoeff (entries w)).val x=_
    rw [first,ih]

omit [FiniteDimensional ℝ K] in
theorem hot (w : Rail G I) : ContDiffAt ℝ ω (deposited (K:=K) w) 0 := (smooth w).contDiffAt

end YM.Integration.WilsonMatrixTicketLanesReflectedJets
