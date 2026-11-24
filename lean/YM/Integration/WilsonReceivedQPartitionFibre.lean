import YM.Integration.WilsonThermometerRegisteredCapturedMaterial
import YM.Integration.WilsonReceivedQNominalWallet

/-! Extract one actual connected group word from the paid captured roster. Its scalar, sites and gauge transports are the ones in the published upper pupil. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedQPartitionFibre
open Function Finset RG Marker Multi Lattice Wilson QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Push Push.AbsoluteSums Push.Local Paths Comparison.RG02.Cumulants Planned.GuardedAtom
open WilsonThermometerRegisteredCapturedLedger WilsonThermometerRegisteredCapturedNames
open WilsonThermometerRegisteredCapturedSector WilsonCapturedPrimarySoftPartition WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators

local notation "J"=>Stock.census (Fin 3)
local notation "D"=>Stock.census Unit
def whole (s:Hot J):↥(shards J s.val):=⟨(parts J).fire s,by simp⟩

private theorem sole (s:Hot J)(f:(J).Mode→ℂ):
    (∏j:Fin (whole s).val.val.card,f (block (whole s).val j))=f s.val:=by
  calc
    _=∏v∈(whole s).val.val,f v.val:=(Equiv.prod_comp (index (whole s).val)
      (fun v:↥(whole s).val.val=>f v.val.val)).trans (prod_coe_sort (whole s).val.val (fun v=>f v.val))
    _=f s.val:=by simp [whole,Census.fire]

variable {G:Gauge} {n:Side} {P:Earn.Passport n (Fin 3)} {α ι:Type} {B:Earn.Passport n Unit}
  (X:ι→Earn.Row P J G α) {σ C:ℝ} {ord seats shelf:ℕ} (ages:Fin 3→ℕ) (w:Fin 3→ℝ)
  (sold:Scene.Armada X w ages σ C ord seats shelf) (spent:∑v:Fin 3,ages v≤14)
  (paths:Fin 3→Walk) (S:Earn.Binder B D) (t:α) (A:Unit→Set ℂ)

abbrev Support (s:Hot J):=Names X (whole s).val
def address (s:Hot J)(u:Support X s):Name X:=⟨s.val,whole s,u⟩
private theorem distinct (s:Hot J):Injective (address X s):=by
  intro a b h
  exact eq_of_heq ((Sigma.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2)

local notation "χ" => (fun _:(J).Mode=>(1:ℂ))
local notation "parentRows"=>material X ages w sold spent paths S t χ (amplitude A)
def rows (s:Hot J)(u:Support X s):Earn.Row B D G (Affinity.Wallet A):=
  (parentRows) (address X s u)

private theorem restrict_budget {ι ε:Type} (f:ε→ι) (inj:Injective f) {a:ι→ℝ} {c:ℝ} (h:SumBudget a c):
    SumBudget (a ∘ f) c:=by
  have sub:=h.2.1.comp_injective inj
  exact ⟨fun z=>h.1 _,sub,(Summable.tsum_le_tsum_of_inj f inj (fun z _=>h.1 z)
    (fun _=>le_rfl) sub h.2.1).trans h.2.2⟩

local notation "M" s:max=>rows X ages w sold spent paths S t A s

theorem earned (s:Hot J) (K:ℕ) (hσ:0≤σ) (reach:∀v,(paths v).length≤K)
    (x:Affinity.Wallet A) (incidence:∀v,stop S.center (paths v)=P.origin v)
    (unit:∀v,‖amplitude A v‖≤1) {work capacity horizon:ℕ} (hc:1≤capacity)
    (hh:21≤horizon) (hw:3*ord≤work):
    Scene.Armada (M s) (fun _=>1) (fun _=>21) σ (total (ord:=ord) (σ:=σ) (C:=C) w S χ K)
      work capacity horizon ∧ Tableau (fun _:Unit=>(⊥:Submodule ℝ ℂ)) A (M s):=by
  have bank:=WilsonThermometerRegisteredCapturedLedger.original X ages w sold spent paths S t χ (amplitude A)
    K hσ reach x incidence unit hc hh
  have linear:=WilsonThermometerRegisteredCapturedSector.original X ages w sold spent paths S t χ A
  refine ⟨⟨bank.toMinistry,bank.positive,fun y=>restrict_budget (address X s) (distinct X s)
    (bank.suggests y),⟨fun z=>bank.purchases.spend (address X s z),
    fun z=>⟨(bank.purchases.usable (address X s z)).1.trans hw,(bank.purchases.usable (address X s z)).2⟩⟩,fun z=>bank.honor (address X s z)⟩,
    ⟨fun z=>linear.1 (address X s z)⟩⟩

theorem observed (s:Hot J) (g:ℝ) (hg:g≠0) (x:Affinity.Wallet A) (U:Config G n)
    (incidence:∀v,stop S.center (paths v)=P.origin v) (unit:∀v,‖amplitude A v‖≤1)
    (b:BudgetPoint) {fee a:ℝ} (ha:0≤a) (purchased:Gross (rendered X b g) w b.B a fee):
    HasSum (fun z:Support X s=>((M s) z).nominal g x U)
      (amplitude A x*(bare (rendered X b g) t U).part s.val):=by
  let q:=whole s
  let bank:=bare (rendered X b g) t U
  have old:=WilsonPlantedOrdinaryRoster.full (rendered X b g) t (block q.val) U w sold.positive ha purchased
  rw [←sole s bank.part,←one_mul (amplitude A x)]
  apply (old.mul_left ((1:ℂ)*amplitude A x)).congr_fun
  intro z
  simp only [WilsonCenteredCaptureRegularAtoms.nominal,Finset.prod_apply]
  exact (WilsonThermometerRegisteredCapturedBucket.original X ages w sold spent paths S t (1:ℂ)
    (amplitude A) q.val q.property g hg x U incidence unit z).1

end YM.Integration.WilsonReceivedQPartitionFibre
