import YM.Integration.WilsonIndependentFittedShrinePair

/-! The ballot's own finite fitted tally before numerical evaluation. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentFittedShrineSalary
open Finset Lattice RG Wilson Source Labels PhysicalNext.Repeat.Legato XSpace XSpace.Rose XSpace.Cirrus
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Bank WilsonCoeffUV.Power PowerSeries PertExtension Orb.SlotEvaluation FVA2
open Function Matrix Laurent Bloch Metric FreeResolvent Work.F08 Tree
open Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source.Drops Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Ore
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedTopFilm (dose)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G)(survey:Bool){d h e k m:ℕ}(w:d<h)
variable (H:Hol G)(v:Rails d k m e)(E A K U:Credit)
local notation "F" => R.family.labels.level d

theorem grade (L:CutsP H (sectionAt R W survey d) w v E A K U)(b:Volume h)(a:Alma F)(j:ℕ):
    ‖coeff j (dose R w L.tileP b a)‖=‖coeff j (L.tileP a)‖*|jewelBloom w a b|:=by
  simp only [dose,coeff_mul_C,FVA2.TaylorWick.into,coeff_map,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  change ‖((coeff j (L.tileP a):ℝ):ℂ)‖*_=_
  rw [Complex.norm_real,Real.norm_eq_abs]

/-- One genuine credit is quoted before the selected joint top, its axis, and all input coefficients. -/
theorem original:
    ∃V:Credit,∀L:CutsP H (sectionAt R W survey d) w v E A K U,
      ∀b:Volume h,∀Q≤e,∀a:Alma F,
        belt Q (dose R w L.tileP b a)≤((Q+1:ℕ):ℝ)*(V.buy L.Age*L.fuel)*|jewelBloom w a b|:=by
  obtain ⟨V,fees⟩:=CutsP.stature H (sectionAt R W survey d) w v E A K U
  refine ⟨V,?_⟩
  intro L b Q cap a
  unfold WilsonPhysicalMarkedDefect.RawProduct.belt
  calc
    _≤∑j∈range (Q+1),(V.buy L.Age*L.fuel)*|jewelBloom w a b|:=by
      apply sum_le_sum
      intro j hj
      rw [grade]
      exact mul_le_mul_of_nonneg_right
        (fees L j ((Nat.le_of_lt_succ (mem_range.mp hj)).trans cap) a).main (abs_nonneg _)
    _=_:=by rw [sum_const,card_range,nsmul_eq_mul];ring

theorem portfolio:
    ∃V:Credit,∀L:CutsP H (sectionAt R W survey d) w v E A K U,
      ∀b:Volume h,∀Q≤e,
        (∑a:Alma F,belt Q (dose R w L.tileP b a))≤
        ((Q+1:ℕ):ℝ)*(V.buy L.Age*L.fuel)*(∑a:Alma F,|jewelBloom w a b|):=by
  obtain ⟨V,submitted⟩:=original R W survey w H v E A K U
  refine ⟨V,fun L b Q cap=>?_⟩
  rw [mul_sum]
  exact sum_le_sum fun a _=>submitted L b Q cap a

end YM.Integration.WilsonIndependentFittedShrineSalary
