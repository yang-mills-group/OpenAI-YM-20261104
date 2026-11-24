/- The rows of one genuine face partition, published before testing the new scalar name. -/
import YM.Integration.WilsonThermometerRegisteredCapturedNames
import YM.Integration.WilsonThermometerRegisteredCapturedExpense

noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCapturedBucket
open RG Marker Multi Lattice Wilson QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene Finset
open Push Push.AbsoluteSums Push.Local Paths
open Comparison.RG02.Cumulants Push.AbsoluteSums
open WilsonThermometerRegisteredCapturedRoster WilsonThermometerRegisteredCapturedNames
open WilsonCapturedPrimarySoftPartition
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {P:Earn.Passport n (Fin 3)} {R:Census (Fin 3)} {α ξ ι:Type}
variable {B:Earn.Passport n Unit} {D:Census Unit} (X:ι→Earn.Row P R G α)
variable {σ C:ℝ} {ord seats shelf:ℕ} (ages:Fin 3→ℕ) (w:Fin 3→ℝ)
variable (sold:Scene.Armada X w ages σ C ord seats shelf) (spent:∑v:Fin 3,ages v≤14)
variable (paths:Fin 3→Walk) (S:Earn.Binder B D) (t:α) (χ:ℂ) (test:ξ→ℂ)
variable {s:R.Mode} (q:(parts R).Mode) (h:q∈shards R s)
def deposited (u:Names X q) : Earn.Row B D G ξ:=
  row paths S (roster X q u) 21 (by decide)
    (WilsonThermometerRegisteredCapturedNames.original X q h ages sold.purchases spent u).1 σ t χ test

def invoice (K:ℕ):ℝ:=
  (max 1 ‖χ‖*Real.exp (σ*((S.length+2*(3*ord+17)*K:ℕ):ℝ)))*
    ∏j:Fin q.val.card,(Poly.toll w (block q j))⁻¹*(3*C)

local notation "T"=>deposited X ages w sold spent paths S t χ test q h
theorem price (K:ℕ) (hσ:0≤σ) (reach:∀v,(paths v).length≤K) :
    SumBudget (fun u=>(T u).height σ) (invoice (ord:=ord) (σ:=σ) (C:=C) w S χ q K):=by
  have old:=WilsonThermometerRegisteredCapturedOffers.original X w sold.positive sold.suggests (block q)
  have pos:0 ≤ max 1 ‖χ‖*Real.exp (σ*((S.length+2*(3*ord+17)*K:ℕ):ℝ)):=by positivity
  apply sumBudget_mono (budget_scale pos old) _ _ le_rfl
  · intro u
    exact mul_nonneg (T u).sound.le (Real.exp_pos _).le
  · intro u
    have quoted:=WilsonThermometerRegisteredCapturedNames.original X q h ages sold.purchases spent u
    have actual:=WilsonThermometerRegisteredCapturedExpense.original paths S (roster X q u)
      21 (by decide) quoted.1 σ t χ test K (3*ord+17) hσ reach quoted.2.1
    simpa only [deposited,roster,List.map_ofFn,List.prod_ofFn,Function.comp_apply] using actual

theorem original (g:ℝ) (hg:g≠0) (x:ξ) (U:Config G n)
    (incidence:∀v,stop S.center (paths v)=P.origin v) (unit:∀v,‖test v‖≤1) (u:Names X q):
    (T u).nominal g x U=χ*test x*∏j:Fin q.val.card,(X (u j).val).nominal g t U ∧
      (T u).Graceful σ ∧ (T u).Budget ∧ (T u).lamp.e≤3*ord ∧ (T u).lamp.toll=21 :=by
  have quoted:=WilsonThermometerRegisteredCapturedNames.original X q h ages sold.purchases spent u
  have legal : ∀z∈roster X q u,z.Graceful σ ∧ z.Budget:=by
    intro z hz
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hz
    exact ⟨sold.purchases.spend _,sold.honor _⟩
  obtain ⟨eq,regular,pay,_,degree_eq,_,toll⟩:=
    WilsonThermometerRegisteredCapturedRoster.original paths S (roster X q u) 21 (by decide)
      quoted.1 σ t χ test g hg U x incidence legal unit
  refine ⟨?_,regular,pay,degree_eq.le.trans quoted.2.2,toll⟩
  simpa only [deposited,coefficient,roster,List.map_ofFn,List.prod_ofFn,Function.comp_apply] using eq
end YM.Integration.WilsonThermometerRegisteredCapturedBucket
