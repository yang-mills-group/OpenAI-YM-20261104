import YM.Integration.WilsonThermometerSameWalkCatalogue
import YM.Integration.WilsonThermometerSameWalkWindow
import YM.Integration.WilsonRegisteredLogFare

/-! Actual moving-order rooted tariff of the deposited core and rank-zero row.
The finite stencil is fixed before the period. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkSectionFare
open PhysicalNext.Repeat.Legato
open Function Filter Finset Lattice Wilson RG Labels Source ConnectedActivityE6
open Push.Local Push.AbsoluteSums AnalyticNext WilsonRetainedMarkedInletRegular
open QuadraticLocal QuadraticLocal.Earn Marker WilsonOriginalStarPrimaryCatalog ActualRunPhysicalPages
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" => R.family
local notation "S₀" => R.family.localSection d
local notation "F₀" => R.family.labels.level d
local notation "β" i:max => R.family.path.levels.clock.hatBeta i

private theorem columns (simple:G.Simple) (pace:WilsonWindowReportingPace.Slow R.kit):
    ∀ᶠ i:ℕ in atTop,((C₀).path.levels.params i).columns ≤ (β i)^2:=by
  obtain ⟨a,ha⟩:=eventually_atTop.mp (WilsonRegisteredLogFare.column R simple pace.2)
  filter_upwards [eventually_ge_atTop (a+1),(RG01.Physical.hats simple (C₀).path.levels).eventually_ge_atTop 2]
    with i ready hi
  obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have h:=ha j (by omega)
  have log:=Real.log_le_self (x:=β (j+1)) (by linarith)
  nlinarith only [h,log,hi,mul_nonneg (sub_nonneg.mpr hi) (show 0≤β (j+1) by linarith)]

theorem original (simple:G.Simple) (pace:WilsonWindowReportingPace.Slow R.kit)
    (book:WilsonReportLampForecast.Ready (C₀).path.levels):
    ∀ᶠ i:ℕ in atTop,∀N per:ℕ,i ≤ N → ((C₀).path.levels.params i).supportExponent=100 →
      ∀{V:Type} (o:V→Site ((C₀).side i per)) (j:V) (v:(C₀).label d) (w:V→ℝ),0≤w j →
      rent R N per i d o j v w (100+1+1) ≤ (β i)^6*(w j*(F₀).coeffSize v):=by
  let K:=atomTiles (S₀)
  filter_upwards [columns R simple pace,WilsonThermometerSameWalkWindow.original R simple book,
    (RG01.Physical.hats simple (C₀).path.levels).eventually_ge_atTop (max (2:ℝ) (Real.exp (103*K)))]
    with i col cash hi N per live support V o j v w wpos
  let P:=(C₀).path.rep N per i
  let ell:=coverNumber P.p.B ((S₀).footprint (o j))
  have date:P.p=(C₀).path.levels.budget i:=(R.makes.wilson.represents N per i live).vac
  have fixed:P.p.supportExponent=100:=by rw [date];exact support
  have count:ell≤K:=atomTiles_price (S₀) P.p (o j)
  have late:Real.exp (103*(K:ℝ)) ≤ β i:=(le_max_right _ _).trans hi
  have two:(2:ℝ) ≤ β i:=(le_max_left _ _).trans hi
  have one:1 ≤ β i:=by linarith
  have pos:0 ≤ β i:=by linarith
  have printed:cost P.p ≤ (β i)^2:=by
    simpa [WilsonThermometerSameWalkWindow.length] using (cash per P date 0).1
  have width:Real.exp (103*(ell:ℝ)) ≤ β i:=(Real.exp_le_exp.mpr (by exact_mod_cast Nat.mul_le_mul_left 103 count)).trans late
  have extra:Real.exp ((100+1+1)*(ell:ℝ)) ≤ β i:= (Real.exp_le_exp.mpr (by linarith [show 0≤(ell:ℝ) by positivity] :
    (100+1+1)*(ell:ℝ) ≤ 103*ell)).trans width
  have native:=allowance P.p ell
  have stronger:moving P.p ell*Real.exp ((100+1+1)*(ell:ℝ)) ≤ (β i)^3:=by
    calc _ = (moving P.p ell*Real.exp ((P.p.supportExponent-1)*ell))*Real.exp (3*ell) := by
                rw [fixed,mul_assoc,←Real.exp_add];congr 2;ring
         _ ≤ (cost P.p*Real.exp (P.p.supportExponent*ell))*Real.exp (3*ell) :=
                mul_le_mul_of_nonneg_right native (Real.exp_pos _).le
         _ = cost P.p*Real.exp (103*(ell:ℝ)):=by rw [fixed,mul_assoc,←Real.exp_add];congr 2;ring
         _ ≤ (β i)^2*(β i):=mul_le_mul printed width (Real.exp_pos _).le (sq_nonneg _)
         _ = _:=by ring
  have norm:0≤(F₀).coeffSize v:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have core:price R i d ((F₀).core v) ≤ (β i)^2*(F₀).coeffSize v:=mul_le_mul col
    (Work.G08.size_core (F₀) _) (Finset.sum_nonneg fun _ _=>norm_nonneg _) (sq_nonneg _)
  have ppos:0 ≤ price R i d ((F₀).core v):=mul_nonneg (zero_le_one.trans ((C₀).path.levels.params i).columns_ge)
    (Finset.sum_nonneg fun _ _=>norm_nonneg _)
  have unit:‖v 0‖ ≤ (F₀).coeffSize v:=Finset.single_le_sum (f:=fun i=>‖v i‖) (fun _ _=>norm_nonneg _) (Finset.mem_univ _)
  have reg: moving P.p ell*Real.exp ((100+1+1)*(ell:ℝ)) * price R i d ((F₀).core v) ≤ (β i)^5*(F₀).coeffSize v:=by
    calc _ ≤ (β i)^3*((β i)^2*(F₀).coeffSize v):=mul_le_mul stronger core ppos (pow_nonneg pos _)
         _ = _ := by ring
  have scalar:‖v 0‖*Real.exp ((100+1+1)*(ell:ℝ)) ≤ (β i)^5*(F₀).coeffSize v:=by
    calc _ ≤ (F₀).coeffSize v*(β i) :=mul_le_mul unit extra (Real.exp_pos _).le norm
         _ ≤ (F₀).coeffSize v*(β i)^5:=mul_le_mul_of_nonneg_left (by simpa using pow_le_pow_right₀ one (show 1≤5 by decide)) norm
         _ = _ := by ring
  rw [rent,Fintype.sum_bool]
  simp only [amount,Bool.false_eq_true,if_false]
  change w j * ‖v 0‖ * Real.exp ((100+1+1)*(ell:ℝ)) +
    w j * (moving P.p ell * price R i d ((F₀).core v)) * Real.exp ((100+1+1)*(ell:ℝ)) ≤ _
  calc _ = w j*(‖v 0‖*Real.exp ((100+1+1)*(ell:ℝ))+(moving P.p ell*Real.exp ((100+1+1)*(ell:ℝ)))*price R i d ((F₀).core v)):=by ring
       _ ≤ w j*((β i)^5*(F₀).coeffSize v+(β i)^5*(F₀).coeffSize v):=mul_le_mul_of_nonneg_left (add_le_add scalar reg) wpos
       _ = 2*(β i)^5*(w j*(F₀).coeffSize v):=by ring
       _ ≤ (β i)*(β i)^5*(w j*(F₀).coeffSize v):=by gcongr
       _ = _:=by ring

end YM.Integration.WilsonThermometerSameWalkSectionFare
end
