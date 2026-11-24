/- The one-slot intake is the original ordinary response at its own measured coupling. -/
import YM.Integration.WilsonThermometerRegisteredCapturedPace
import YM.Integration.WilsonThermometerCenteredAlgebra

noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCapturedUncut
open Finset RG Marker Multi Lattice Wilson QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Push Push.Local
open Planned.GuardedAtom Extra.Trajectories Primitives.GCC.Anchor Comparison.RG02
open WilsonThermometerRegisteredCapturedPace WilsonThermometerRegisteredCapturedSector
open WilsonThermometerRegisteredCapturedLedger WilsonThermometerCenteredAlgebra WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators
local notation "J"=>Stock.census (Fin 3)
local notation "K"=>Stock.census Unit
variable {G:Gauge} {n:Side} {P:Earn.Passport n (Fin 3)} {α ι:Type}
variable {B:Earn.Passport n Unit} (X:ι→Earn.Row P J G α) (r:ℝ) (hr:0<r)
variable {σ C:ℝ} {ord seats shelf:ℕ} (ages:Fin 3→ℕ) (w:Fin 3→ℝ)
variable (sold:Scene.Armada X w ages σ C ord seats shelf) (spent:∑v:Fin 3,ages v≤14)
variable (paths:Fin 3→Walk) (S:Earn.Binder B K) (t:α) (Q:Poly J) (A:Unit→Set ℂ)
def weights (s:(J).Mode):ℂ:=Q.part (complement s)
local notation "X'"=> (fun z=>returned r hr (X z))
local notation "sold'"=>WilsonThermometerRegisteredCapturedPace.original r hr X w ages sold
def submitted : Name X'→Earn.Row B K G (Affinity.Wallet A):=
  material X' ages w sold' spent paths S t (weights Q) (amplitude A)
local notation "M"=>submitted X r hr ages w sold spent paths S t Q A

theorem shifted {g:ℝ} (b:BudgetPoint) {fee a:ℝ} (purchased:Gross (rendered X b (r*g)) w b.B a fee):
    Gross (rendered X' b g) w b.B a fee:=by
  obtain ⟨f,pos,pay,bill⟩:=purchased
  refine ⟨f,pos,?_,bill⟩
  intro z x U
  change ‖(returned r hr (X z)).nominal g x U‖≤f z
  rw [evaluated]
  exact pay z x U

theorem moved {g:ℝ} (b:BudgetPoint) (U:Config G n):
    bare (rendered X' b g) t U=bare (rendered X b (r*g)) t U:=by
  unfold WilsonRootedKioskOccupiedSlip.bare
  apply tsum_congr
  intro z
  congr 1
  exact evaluated r hr (X z) g t U

theorem observed (g:ℝ) (hg:g≠0) (x:Affinity.Wallet A) (U:Config G n)
    (incidence:∀v,stop S.center (paths v)=P.origin v) (unit:∀y,‖amplitude A y‖≤1)
    (b:BudgetPoint) {fee a:ℝ} (ha:0≤a) (purchased:Gross (rendered X b (r*g)) w b.B a fee):
    HasSum (fun z=>(M z).nominal g x U)
      ((amplitude A x)*((Poly.pass (bare (rendered X b (r*g)) t U))*Q).part full):=by
  have launched:=WilsonThermometerRegisteredCapturedReading.original X' ages w sold' spent paths S t
    (weights Q) (amplitude A) g hg x U incidence unit b ha (shifted X r hr w b purchased)
  rw [moved X r hr t b U] at launched
  convert launched using 1
  · rfl
  have complete:∀s b:(J).Mode, Poly.merges s b full ↔ b=complement s:=by decide
  rw [Poly.part_mul]
  simp only [complete,Finset.sum_ite_eq',mem_univ,if_true,weights,Finset.mul_sum]
  apply sum_congr rfl
  intro z _
  ring

theorem original (g:ℝ) (hg:g≠0) (x:Affinity.Wallet A) (U:Config G n)
    (incidence:∀v,stop S.center (paths v)=P.origin v) (unit:∀y,‖amplitude A y‖≤1)
    (b:BudgetPoint) {fee a:ℝ} (ha:0≤a) (purchased:Gross (rendered X b (r*g)) w b.B a fee):
    Spill.Foundry.uncut M g x U=Poly.send ((K).fire ())
      ((amplitude A x)*((Poly.pass (bare (rendered X b (r*g)) t U))*Q).part full):=by
  have read:=observed X r hr ages w sold spent paths S t Q A g hg x U incidence unit b ha purchased
  have single:S.mode=(K).fire ():=by
    apply Subtype.ext
    have home:S.mode.val=univ:=eq_univ_of_forall fun v=>(Subsingleton.elim v S.front) ▸ S.east
    simp [home,Census.fire]
  let z:=(K).fire ()
  have at_mode(u:Name X'):(M u).mode=z:=single
  have atom(c:ℂ):c • Poly.send z 1=Poly.send z c:=by
    ext m
    simp only [Poly.part_smul,Poly.part_send]
    split_ifs <;> simp
  have result:=read.smul_const (Poly.send z 1)
  simp_rw [atom] at result
  change (∑'u,Poly.send ((M u).mode) ((M u).nominal g x U))=_
  simp_rw [at_mode]
  exact result.tsum_eq
end YM.Integration.WilsonThermometerRegisteredCapturedUncut
