import YM.Integration.WilsonRootedPosteriorObserved

/-! One uniform tariff of the original curved posterior's complete
centered row, at every fine field and every held coarse field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedPosteriorWallet
open Filter Function Finset MeasureTheory Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree
open Pressure Pressure.Testing Next.SectorChange Push.SectorMeasure
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open IterationFour IterationFour.Vacuum WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonRootedPosteriorDifferences (law relative)
open WilsonRootedPosteriorObserved (slot row)
open scoped Topology BigOperators Classical
variable {G:Gauge}{I:Type}[DecidableEq I]{Γ:Census I}(R:Run G)(d:LocalFormal.Datum R.family Γ)
local notation "coarse" => R.family.side d.level d.period
local notation "fine" => R.family.side (d.level+1) d.period
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)

theorem deposited (f:Config G fine→ℂ)(hf:Measurable f):
    Measurable (fun V:Config G coarse=>∫U,f U ∂law R d V):=by
  let den:=actualConditionalDensity R.family d.cutoff d.period d.level
  have hd:=ActualWilsonConditionalRoots.density_meas R.family (p:=d.period) R.makes d.below
  have named (V:Config G coarse):(∫U,f U ∂law R d V)=∫U,den V U • f U ∂prior G fine:=by
    rw [WilsonRootedPosteriorDifferences.law,ActualWilsonConditionalRoots.average R.family R.makes d.below V]
    rfl
  simp only [named]
  exact (hd.smul (hf.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

theorem measurable (incoming:Actual.Lit Γ (Config G fine))(floor:Actual.Floor P incoming)(a b:I)
    (legal:({a,b}:Finset I)∈Γ.choices):Measurable (row R d incoming a b legal):=by
  let r:=slot R d incoming
  let e:=fun (s:Γ.Mode)(V:Config G coarse)=>∫U,r s U ∂law R d V
  have reading (s:Γ.Mode):Measurable (r s):=(WilsonRootedPosteriorDifferences.admissible R d _ (floor.safe s)).meas
  have old (s:Γ.Mode):Measurable (e s):=deposited R d _ (reading _)
  have one (s:Γ.Mode):Measurable (fun X:Config G coarse×Config G fine=>r s X.2-e s X.1):=
    ((reading s).comp measurable_snd).sub ((old s).comp measurable_fst)
  exact (((one _).sub (((old _).comp measurable_fst).mul (one _)))).sub (((old _).comp measurable_fst).mul (one _))

def fee (f:Γ.Mode→ℝ)(a b:I)(legal:({a,b}:Finset I)∈Γ.choices):ℝ:=
  2*f ⟨{a,b},legal⟩+4*f (Γ.fire a)*f (Γ.fire b)

theorem charged (incoming:Actual.Lit Γ (Config G fine))(floor:Actual.Floor P incoming)(f:Γ.Mode→ℝ)
    (pos:∀s,0≤f s)(cash:∀s U,‖Actual.atMark s incoming U‖≤f s*(P).eval U)(a b:I)
    (legal:({a,b}:Finset I)∈Γ.choices)(X:Config G coarse×Config G fine):
    ‖row R d incoming a b legal X‖≤fee f a b legal:=by
  let r:=slot R d incoming
  let e:=fun (s:Γ.Mode)=>∫U,r s U ∂law R d X.1
  have source(s:Γ.Mode):‖r s X.2‖≤f s:=by
    change ‖Actual.atMark s incoming X.2/((P).eval X.2:ℂ)‖≤f s
    have h:=(Normal.actual R.family.path R.makes.wilson d.cutoff d.period (d.level+1) d.below).positive X.2
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos h,div_le_iff₀ h]
    exact cash s X.2
  have moved(s:Γ.Mode):‖e s‖≤f s:=by
    change ‖∫U,relative R d (Actual.atMark s incoming) U ∂law R d X.1‖≤f s
    rw [WilsonRootedPosteriorDifferences.amount]
    exact WilsonRootedNonflatIncome.spend R d X.1 _ (floor.safe s) (cash s)
  have center(s:Γ.Mode):‖r s X.2-e s‖≤2*f s:=(norm_sub_le _ _).trans (by linarith [source s,moved s])
  let A:=Γ.fire a
  let B:=Γ.fire b
  let J:Γ.Mode:=⟨{a,b},legal⟩
  let c:=fun s:Γ.Mode=>r s X.2-e s
  change ‖c J-e B*c A-e A*c B‖≤_
  calc
    _ ≤ ‖c J‖+‖e B*c A‖+‖e A*c B‖:=(norm_sub_le _ _).trans (add_le_add (norm_sub_le ..) le_rfl)
    _ ≤ 2*f J+f B*(2*f A)+f A*(2*f B):=by
      simp only [norm_mul]
      exact add_le_add (add_le_add (center J) (mul_le_mul (moved B) (center A) (norm_nonneg _) (pos B)))
        (mul_le_mul (moved A) (center B) (norm_nonneg _) (pos A))
    _ = _:=by unfold fee; dsimp only [A,B,J]; ring

section analytic
variable [Fintype I]{J:Request I}{sched:NumericSchedule R.family J}(F:AnalyticInput J sched d)(test:TestSpace J.tests)
local notation "Πₛ" => ManuscriptQLocalActualLog.source R d F test
theorem issued:∃f:Γ.Mode→ℝ,(∀s,0≤f s) ∧ ∀a b (legal:({a,b}:Finset I)∈Γ.choices),
    Measurable (row R d (Πₛ) a b legal) ∧ ∀X,‖row R d (Πₛ) a b legal X‖≤fee f a b legal:=by
  obtain ⟨f,pos,cost⟩:=WilsonRootedNonflatIncome.issued R d F test
  exact ⟨f,pos,fun a b legal=>⟨measurable R d _ (ManuscriptQLocalActualLog.floor R d F test) a b legal,
    charged R d _ (ManuscriptQLocalActualLog.floor R d F test) f pos cost a b legal⟩⟩
end analytic
end YM.Integration.WilsonRootedPosteriorWallet
