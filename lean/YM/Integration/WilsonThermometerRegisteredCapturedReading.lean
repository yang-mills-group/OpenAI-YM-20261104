/- Sum the genuine scalar row before the next integration. The empty face contributes at its own site. -/
import YM.Integration.WilsonThermometerRegisteredCapturedLedger
import YM.Integration.WilsonPlantedOrdinaryRoster

noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCapturedReading
open Finset RG Marker Multi Lattice Wilson QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Push Push.AbsoluteSums Push.Local Paths Comparison.RG02.Cumulants Planned.GuardedAtom
open WilsonThermometerRegisteredCapturedLedger WilsonThermometerRegisteredCapturedNames
open WilsonCapturedPrimarySoftPartition WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators
private theorem collected {J:Type} [Fintype J] {I:J→Type} (f:(Σj,I j)→ℂ) (v:J→ℂ)
    (income:∀j,HasSum (fun z=>f ⟨j,z⟩) (v j)):HasSum f (∑j,v j):=by
  have hn:Summable (fun z=>‖f z‖):=(summable_sigma_of_nonneg (fun z=>norm_nonneg (f z))).2
    ⟨fun j=>(income j).summable.norm,(hasSum_fintype _).summable⟩
  have h:Summable f:=hn.of_norm
  have total:(∑'z,f z)=∑j,v j:=by
    rw [h.tsum_sigma]
    simp_rw [(income _).tsum_eq]
    exact tsum_fintype _
  exact total ▸ h.hasSum

variable {G:Gauge} {n:Side} {P:Earn.Passport n (Fin 3)} {R:Census (Fin 3)} {α ξ ι:Type}
variable {B:Earn.Passport n Unit} {D:Census Unit} (X:ι→Earn.Row P R G α)
variable {σ C:ℝ} {ord seats shelf:ℕ} (ages:Fin 3→ℕ) (w:Fin 3→ℝ)
variable (sold:Scene.Armada X w ages σ C ord seats shelf) (spent:∑v:Fin 3,ages v≤14)
variable (paths:Fin 3→Walk) (S:Earn.Binder B D) (t:α) (χ:R.Mode→ℂ) (test:ξ→ℂ)
local notation "M"=>material X ages w sold spent paths S t χ test

theorem original (g:ℝ) (hg:g≠0) (x:ξ) (U:Config G n)
    (incidence:∀v,stop S.center (paths v)=P.origin v) (unit:∀v,‖test v‖≤1)
    (b:BudgetPoint) {fee a:ℝ} (ha:0≤a) (purchased:Gross (rendered X b g) w b.B a fee):
    HasSum (fun u:Name X=>(M u).nominal g x U)
      (∑s:R.Mode,χ s*test x*(Poly.pass (bare (rendered X b g) t U)).part s):=by
  let bank:=bare (rendered X b g) t U
  have quiet : bank.part R.quiet=0:=WilsonRootedKioskCompleteFiling.quiet
    (rendered X b g) sold.positive ha purchased t U
  let cost (s:R.Mode) (q:↥(shards R s)):=χ s*test x*∏j:Fin q.val.val.card,bank.part (block q.val j)
  let observed(u:Name X):=(M u).nominal g x U
  have fibre(s:R.Mode)(q:↥(shards R s)):HasSum (fun z=>observed ⟨s,q,z⟩) (cost s q):=by
    have old:=WilsonPlantedOrdinaryRoster.full (rendered X b g) t (block q.val) U w sold.positive ha purchased
    apply (old.mul_left (χ s*test x)).congr_fun
    intro z
    simp only [WilsonCenteredCaptureRegularAtoms.nominal,Finset.prod_apply]
    exact (WilsonThermometerRegisteredCapturedBucket.original X ages w sold spent paths S t (χ s)
      test q.val q.property g hg x U incidence unit z).1
  have compose(s:R.Mode): (∑q,cost s q)=χ s*test x*(Poly.pass bank).part s:=by
    have split (q:(parts R).Mode):
        (∏j:Fin q.val.card,bank.part (block q j))=∏v∈q.val,bank.part v.val:=
      (Equiv.prod_comp (index q) (fun v:↥q.val=>bank.part v.val.val)).trans
        (Finset.prod_coe_sort q.val (fun v=>bank.part v.val))
    unfold cost
    rw [pass_partition _ quiet]
    simp_rw [split]
    rw [←mul_sum]
    exact congrArg (fun t:ℂ=>χ s*test x*t) (Finset.sum_coe_sort (shards R s)
      (fun z=>∏v∈z.val,bank.part v.val))
  apply collected observed
  intro s
  rw [←compose]
  exact collected (fun z=>observed ⟨s,z⟩) (cost s) (fibre s)
end YM.Integration.WilsonThermometerRegisteredCapturedReading
