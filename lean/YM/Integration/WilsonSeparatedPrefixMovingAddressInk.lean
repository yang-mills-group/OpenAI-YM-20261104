import YM.Integration.WilsonSeparatedPrefixMovingAddressPage

/-! The actual test-page algebra and its pullback through native child maps. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingAddressInk
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical ContDiff
open WilsonCoeffUV.Layout


open WilsonSeparatedPrefixMovingAddressPage (axes tariff multiply funded)
variable {D:ℕ}
private theorem buy (f:Scroll D):∃T:Volume D→L[ℝ]Volume D,(∀g:Scroll D,T (page D g)=page D (multiply f g)) ∧
    ‖T‖≤tariff D*((4:ℝ)^D*‖page D f‖):=by
  apply funded _ _ (by positivity)
  intro j hj z
  exact (axes f hj z).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) (norm_nonneg _))
private def raw (f:Scroll D):Volume D→L[ℝ]Volume D:=(buy f).choose
private theorem named (f g:Scroll D):raw f (page D g)=page D (multiply f g):=(buy f).choose_spec.1 g
private theorem commute (f g:Scroll D):raw f (page D g)=raw g (page D f):=by
  rw [named,named];congr 1;exact Subtype.ext (funext fun x=>mul_comm (f.val x) (g.val x))
def writer (u:Volume D):Volume D→L[ℝ]Volume D:=raw (submitted u).choose
theorem print (f g:Scroll D):writer (page D f) (page D g)=page D (multiply f g):=by
  rw [writer,commute,(submitted _).choose_spec,←commute f g,named]
theorem charge (u:Volume D):‖writer u‖≤tariff D*((4:ℝ)^D*‖u‖):=by
  have bound:=(buy (submitted u).choose).choose_spec.2
  exact bound.trans_eq (congr_arg (fun a:Volume D=>tariff D*((4:ℝ)^D*‖a‖)) (submitted u).choose_spec)

theorem child (P:Patch)(k:Site P.L)(u v:Volume D):
    foldWord P k D (writer u v)=writer (foldWord P k D u) (foldWord P k D v):=by
  obtain ⟨f,rfl⟩:=submitted u
  obtain ⟨g,rfl⟩:=submitted v
  rw [print,observed,observed,observed,print];rfl

abbrev Address:=(P:Patch)×Site P.L
def along (D:ℕ):List Address→Volume D→L[ℝ]Volume D
  | []=>ContinuousLinearMap.id ℝ (Volume D)
  | a::rest=>(along D rest).comp (foldWord a.1 a.2 D)

theorem route (path:List Address)(u v:Volume D):along D path (writer u v)=writer (along D path u) (along D path v):=by
  induction path generalizing u v with
  | nil=>rfl
  | cons a rest ih=>
    change along D rest (foldWord a.1 a.2 D (writer u v))=_
    rw [child,ih];rfl

theorem invoice (path:List Address)(u:Volume D):‖writer (along D path u)‖≤tariff D*((4:ℝ)^D*‖u‖):=by
  have small (v:Volume D):‖along D path v‖≤‖v‖:=by
    induction path generalizing v with
    | nil=>exact le_rfl
    | cons a rest ih=>
      apply (ih (foldWord a.1 a.2 D v)).trans
      exact ((foldWord a.1 a.2 D).le_opNorm v).trans ((mul_le_mul_of_nonneg_right (fold_bound ..) (norm_nonneg _)).trans_eq (one_mul _))
  have cost:0≤tariff D:=by unfold tariff;positivity
  exact (charge _).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (small _) (by positivity)) cost)
end YM.Integration.WilsonSeparatedPrefixMovingAddressInk
