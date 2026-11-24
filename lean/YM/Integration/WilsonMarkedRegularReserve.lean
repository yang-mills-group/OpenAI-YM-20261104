import YM.QuadraticLocal.Display
import YM.QuadraticLocal.Shelter.Shadows

/-! Use the regular support reserve on the actual marked gallery. Only the
auxiliary hard price may depend on the finite period. The physical regular
income and every marked coefficient retain their original normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedRegularReserve
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Ac Marker
open Push.AbsoluteSums Push.Corrected QuadraticLocal RG3.Script.Picnic LocalComparison
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

def raised (p:BudgetPoint) : BudgetPoint :=
  { p with
    supportExponent := p.supportExponent+2
    exponent_pos := by linarith [p.exponent_pos] }

private def school {G:Gauge} {n:Side} (P:Rep G n) : Rep G n := {P with p:=raised P.p}

variable {G:Gauge} {n:Side} {V : Type} [DecidableEq V] {J:Census V} {o:V→Site n}
    {T ι:Type} {P:Rep G n}

private def reserveLamps (L:Lamps T ι G P.p o J) : Lamps T ι G (raised P.p) o J :=
  { mode:=L.mode,live:=L.live,address:=L.address,roots:=L.roots,nominal:=L.nominal,
    legal:=fun t i=>by obtain ⟨a,b,c,d,e⟩:=L.legal t i; exact ⟨a,b,c,d,e⟩,
    clear:=L.clear,pure:=L.pure }

private def reserveHard (K:Hard T P.p P.activities.forced P.activities.K o J) :
    Hard T (raised P.p) P.activities.forced P.activities.K o J :=
  {hard:=K.hard,locality:=fun t i=>by obtain ⟨a,b,c,d⟩:=K.locality t i; exact ⟨a,b,c,d⟩,
   charged:=K.charged,quiet:=K.quiet}

private def gallery (A:Gallery T ι o P J) : Gallery T ι o (school P) J :=
  ⟨reserveLamps A.E,reserveHard A.K⟩

private lemma finite_hard {w:V→ℝ} (hw:∀v,0<w v) (X:ℕ→Support n) (B:ℕ)
    {pay:ℕ→Poly J} {a b:ℝ} (h:Hit X B (fun i=>Poly.price w (pay i)) a b) :
    ∃ C:ℝ, Hit X B (fun i=>Poly.price w (pay i)) (a+2) C := by
  let D := (Finset.univ : Finset (Support n)).sup (coverNumber B)
  let k := Real.exp (2*(D:ℝ))
  have price i : 0≤Poly.price w (pay i) := Finset.sum_nonneg
    (fun s _=>mul_nonneg (Poly.worth hw s).le (norm_nonneg _))
  refine ⟨k*b,fun x=>?_⟩
  apply budget_mono (budget_scale (Real.exp_pos _).le (h x))
  · intro i; split_ifs
    · exact mul_nonneg (price i) (Real.exp_pos _).le
    · exact le_rfl
  · intro i
    dsimp only
    split_ifs
    · have hsize : coverNumber B (X i) ≤ D := Finset.le_sup (f:=coverNumber B) (Finset.mem_univ _)
      have room : Real.exp (2*(coverNumber B (X i):ℝ)) ≤ k :=
        Real.exp_le_exp.mpr (by exact_mod_cast Nat.mul_le_mul_left 2 hsize)
      rw [add_mul,Real.exp_add]
      exact (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left room (Real.exp_pos _).le) (price i)).trans_eq (by ring)
    · simp

theorem original [Fintype V] [Nonempty V] [Nonempty T] [Countable ι]
    (A:Gallery T ι o P J) {w:V→ℝ} {κ e h:ℝ} (hw:∀v,0<w v) (hk:0<κ)
    (valid:P.activities.ForcedFamily P.p)
    (regular:A.E.Paid w P.p.B (P.p.supportExponent+2) e)
    (forced:A.K.Paid w P.p.B P.p.supportExponent h) :
    ∃ f:ℝ, Nonempty (FullBudget (raised P.p) (Display.taste A) w κ (4*e) f) := by
  let A' := gallery A
  have hY : (school P).activities.ForcedFamily (school P).p := by
    obtain ⟨a,b,c,d,e₀,f,g⟩:=valid
    exact ⟨a,b,c,d,e₀,f,g⟩
  have reg : A'.E.Paid w (school P).p.B (school P).p.supportExponent e := by
    obtain ⟨f,hf,hb,hit⟩:=regular.budget
    exact ⟨f,hf,hb,hit⟩
  obtain ⟨pay,covers,hit⟩:=forced.wages
  obtain ⟨cap,hcap⟩:=finite_hard hw (fun i=>(P.activities.forced i).support) P.p.B hit
  have hard : A'.K.Paid w (school P).p.B (school P).p.supportExponent cap :=
    ⟨pay,covers,hcap⟩
  obtain ⟨⟨H⟩,-⟩:= Display.present A' hY hw (le_of_eq (div_mul_cancel₀ cap hk.ne').symm)
    hk (show A'.Pays w (school P).p.supportExponent e cap from ⟨reg,hard⟩)
  refine ⟨cap/κ,⟨?_⟩⟩
  refine ⟨H.white,H.black,H.gold,H.unitBound,?_,H.radii,H.divisor,H.white_nonnegative,
    ?_,?_,H.black_nonnegative,?_,H.gold_nonnegative,H.caption,H.unit_nonnegative,
    ?_,H.regularTotal,H.forcedTotal⟩
  · have small : A.Pays w P.p.supportExponent e h :=
      ⟨Lamps.tenure _ _ hw regular (by linarith),forced⟩
    obtain ⟨⟨base⟩,-⟩ := Display.present A valid hw
      (le_of_eq (div_mul_cancel₀ h hk.ne').symm) hk small
    exact base.active
  · exact fun i => ⟨(H.regular i).controls⟩
  · exact H.regular_law
  · exact H.forced
  · exact H.unit
end YM.Integration.WilsonMarkedRegularReserve
