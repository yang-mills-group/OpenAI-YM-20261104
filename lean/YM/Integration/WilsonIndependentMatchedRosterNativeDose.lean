import YM.Integration.WilsonIndependentMatchedRosterRose
import YM.Integration.WilsonOriginalPhysicalFruitClock
import YM.Integration.WilsonOriginalPhysicalFruitVerse

/-! The column weights selected by the finite bulk course can be used
on the actual physically paid Vane and Ward colors, at their own sites
and cutoff. The two optical scale ratios remain separately identified. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterNativeDose
open Finset Lattice RG Wilson Source Labels Extra.Histories Motion PhysicalNext.Repeat.Legato
open WilsonOriginalPhysicalFruitDose (amounts)
open WilsonOriginalPublicFigureIncome (scale height)
open WilsonReflectedMixedSharpAxis (Cash)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G)
local notation "a" => R.family.S.a
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "S" d:max => R.family.labels.level d

open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace
open WilsonIndependentMatchedSectionIncome
open scoped BigOperators Topology Classical
open Finset WilsonIndependentMatchedFiledIncome

open PowerSeries
open scoped Classical
def gross {d:ℕ}(F:Labels.Frame G d)(e:ℕ)(α:Alma F→ℝ):ℝ:=
  ∑v:Alma F,∑j∈Finset.range (e+1),∑_∈Finset.HasAntidiagonal.antidiagonal j,α v

theorem original (simple:G.Simple){d j f K N per target E:ℕ}(α:Alma (R.family.labels.level d)→ℝ)(paid:∀v,0≤α v)(e:ℕ)(plane:ℂ →L[ℝ] ℝ)(before:j ≤ f)(up:f ≤ K)(live:K ≤ N){η:ℝ}
    (ep:0 ≤ η)(small:η ≤ 1)(A:R.family.label d≃ₗ[ℂ]R.family.label d)(Y:R.family.label d){W:ℝ}
    (cash:Cash (R:=R) d j f K N per target before up live η A Y W)
    (arm:Arm R d N per f K)(same:arm.w=A.symm (fitted R d j N per Y))
    (r g:ℝ)(rp:0<r)(gp:0<g)(ar:a f ≤ r)(t:ℂ)(M roof:ℝ)(mp:0 ≤ M)(one:1 ≤ roof)
    (nn:0 ≤ W)(card:max 1 (2*(a j/a f)^(d+1)*W) ≤ M*(β f)^E)(optical:β K*g^2 ≤ roof):
    WilsonIndependentMatchedFiledIncome.charge e
      (WilsonOriginalPhysicalFruitVerse.written (S d) (amounts R d K N per r t (coords R arm)) plane) α  ≤ 
      gross (S d) e α*‖plane‖*(WilsonOriginalPhysicalFruitClock.salary R d E t M roof*
        (g⁻¹)^WilsonOriginalPhysicalFruitClock.power R d E*(r/a K)^η):=by
  have npos:0 ≤ gross (S d) e α:=Finset.sum_nonneg fun v _=>Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>paid v
  have ins:=WilsonOriginalPhysicalFruitVerse.bought (S d) (amounts R d K N per r t (coords R arm)) plane e α paid
  have price:=WilsonOriginalPhysicalFruitClock.original R simple before up live ep small A Y cash arm same r g rp gp ar t M roof mp one nn card optical
  change _  ≤  gross (S d) e α * _ at ins
  calc _ ≤ gross (S d) e α*(‖plane‖*(S d).coeffSize (amounts R d K N per r t (coords R arm))):=ins
       _ ≤ gross (S d) e α*(‖plane‖*_):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left price (norm_nonneg _)) npos
       _=_:=by ring

/-- Only the actual designated positions bring their physical source
income to a unit-axis hearing. -/
theorem factors {n:ℕ}(flag:Fin (n+1)→Bool)(u b:ℕ)(z:ℝ)(dose rent bound B:Fin (n+1)→ℝ)
    (hz:0 ≤ z)(positive:∀s,0 ≤ rent s)(signed:∀s,rent s ≤ bound s)(weights:∀s,0 ≤ B s):
    WilsonIndependentMatchedRosterReception.perSite u b z (fun s=>WilsonIndependentMatchedRosterAxes.source (flag s) (dose s) (rent s)) B ≤ 
      WilsonIndependentMatchedRosterReception.perSite u b z (fun s=>WilsonIndependentMatchedRosterAxes.source (flag s) (dose s) (bound s)) B:=by
  have cc:0 ≤ WilsonIndependentMatchedRosterTariff.factor u b z:=by unfold WilsonIndependentMatchedRosterTariff.factor;positivity
  apply Finset.prod_le_prod
  · intro s _
    apply mul_nonneg cc;apply mul_nonneg (weights s)
    unfold WilsonIndependentMatchedRosterAxes.source
    dsimp only
    split <;> first | exact mul_nonneg (abs_nonneg _) (positive s) | norm_num
  · intro s _
    apply mul_le_mul_of_nonneg_left _ cc
    apply mul_le_mul_of_nonneg_left _ (weights s)
    unfold WilsonIndependentMatchedRosterAxes.source
    dsimp only
    split <;> first | exact mul_le_mul_of_nonneg_left (signed s) (abs_nonneg _) | exact le_rfl

end YM.Integration.WilsonIndependentMatchedRosterNativeDose
