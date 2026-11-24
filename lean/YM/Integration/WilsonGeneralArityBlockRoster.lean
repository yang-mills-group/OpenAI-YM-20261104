import YM.Integration.WilsonReceivedQPartitionFibre
import YM.Integration.WilsonOriginalStarSceneRows
import YM.Integration.WilsonOriginalPointCompactProgram

/-! Transfer separately filed connected blocks to distinct actual source names and keep each block at its own true center. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonGeneralArityBlockRoster
open Function Finset Lattice Laurent RG Wilson Marker Multi Gauge
open Push Push.AbsoluteSums Push.Local Paths Animals ConnectedActivityE6 QuadraticLocal
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink QuadraticLocal.Affinity
open WilsonRegisteredPairUnaryWallet
open scoped Classical BigOperators

variable {load:ℕ}
local notation "J" => Stock.census (Fin load)
local notation "W" => Stock.census Unit
def room (load:ℕ):Fin load→Set ℂ:=fun _=>disk ()
def project (v:Fin load) (x:Wallet (room load)):Wallet disk:=fun _=>x v
variable {G:Gauge} {n:Side} {I:Type} {O:I→Type} (owner:I→Fin load) (site:Fin load→Site n)
  (X:(i:I)→O i→Earn.Row (Passport.point (fun _:Unit=>site (owner i))) W G (Wallet disk))

local notation "old" z:max=>X (z).1 (z).2
local notation "home" v:max=>WilsonOlderFreshGraphPointWallet.point (site v)
local notation "new" v:max=>WilsonOriginalStarSceneRows.binder site v

def mounted (z:(i:I)×O i):Earn.Row (Passport.point site) J G (Wallet (room load)) where
  binder:=new (owner z.1)
  lamp:=(old z).lamp
  atom:=(old z).atom
  lawful:=(old z).lawful
  clear:=(old z).clear
  salary:=(old z).salary
  sound:=(old z).sound
  paint x:=(old z).paint (project (owner z.1) x)
  rank:=(old z).rank

local notation "M" => mounted owner site X
variable (rooted:∀(i:I)(z:O i),(X i z).binder=WilsonOlderFreshGraphPointWallet.point (site (owner i)))
  (linear:∀i z,∃c:ℂ,∀x:Wallet disk,(X i z).paint x=c*WilsonThermometerRegisteredCapturedSector.amplitude disk x)
local notation "zeros" => (fun _:Fin load=>(⊥:Submodule ℝ ℂ))

theorem located (z:(i:I)×O i):(M z).mode=(J).fire (owner z.1):=rfl
theorem individual (z:(i:I)×O i)(t:Wallet (room load))(g:ℝ)(U:Config G n):
    (M z).nominal g t U=(old z).nominal g (project (owner z.1) t) U:=rfl

include rooted in
theorem height (z:(i:I)×O i)(σ:ℝ):(M z).height σ=(old z).height σ:=by
  change (old z).salary*Real.exp (σ*(((new (owner z.1)).length+(old z).atom.length:ℕ):ℝ))=
    (old z).salary*Real.exp (σ*(((old z).binder.length+(old z).atom.length:ℕ):ℝ))
  rw [rooted]
  simp only [WilsonOlderFreshGraphPointWallet.point,WilsonOriginalStarSceneRows.length]

include linear in
theorem tested:Tableau zeros (room load) M:=by
  constructor
  intro z
  obtain ⟨c,paint⟩:=linear z.1 z.2
  have funEq:(M z).paint=(fun t=>c*(t (owner z.1)).val):=funext fun t=>paint (project (owner z.1) t)
  rw [located,funEq]
  change Attn zeros (room load) {owner z.1} _
  refine ⟨fun t u p=>congrArg (fun y=>c*y) (congrArg Subtype.val (p _ (mem_singleton_self _))),?_,?_⟩
  · intro i hi t x y d a b hd
    obtain rfl:=Finset.mem_singleton.mp hi
    simp only [Function.update_self]
    rw [hd]
    simp only [Complex.real_smul]
    ring
  · intro i hi t ht
    obtain rfl:=Finset.mem_singleton.mp hi
    simp [(Submodule.mem_bot ℝ).mp ht]

variable [Fintype I] (grades:Fin load→ℕ) (cash:I→ℝ) (σ:ℝ) (order seats shelf:ℕ)
  (earned:∀i,Scene.Armada (X i) (fun _:Unit=>1) (fun _:Unit=>grades (owner i)) σ (cash i) order seats shelf)

def invoice (w:Fin load→ℝ):ℝ:=∑i:I,w (owner i)*cash i

include rooted earned in
theorem mounted_salary (w:Fin load→ℝ) (pos:∀v,0<w v) (size:load ≤ seats) (fit:(∑ v:Fin load,grades v) ≤ shelf):
    Scene.Armada M w grades σ (invoice owner cash w) order seats shelf:=by
  have hmode(i:I)(z:O i):(X i z).mode=(W).fire ():=congrArg Earn.Binder.mode (rooted i z)
  have oldPay(i:I):SumBudget (fun z:O i=>(X i z).height σ) (cash i):=by
    have prev:=(earned i).suggests (site (owner i))
    apply sumBudget_mono prev (fun z=>mul_nonneg (X i z).sound.le (Real.exp_pos _).le) _ le_rfl
    intro z
    change _ ≤ (if (X i z).center=site (owner i) then Poly.toll (fun _:Unit=>1) (X i z).mode*(X i z).height σ else 0)
    rw [if_pos (show (X i z).center=site (owner i) from rfl),hmode]
    simp [Poly.toll,Census.fire,Row.height]
  refine ⟨⟨fun s=>(card_le_univ s.val).trans (by simpa using size),fun s=>?_⟩,pos,?_,
    ⟨fun z=>(earned z.1).purchases.spend z.2,?_⟩,fun z t=>(earned z.1).honor z.2 (project _ t)⟩
  · exact (sum_le_sum_of_subset_of_nonneg (f:=grades) (subset_univ s.val) (fun _ _ _=>Nat.zero_le _)).trans (by simpa using fit)
  · intro y
    let f(z:(i:I)×O i):ℝ:=if (M z).center=y then Poly.toll w (M z).mode*(M z).height σ else 0
    have each(i:I):SumBudget (fun z:O i=>f ⟨i,z⟩) (w (owner i)*cash i):=by
      have base:=budget_scale (pos (owner i)).le (oldPay i)
      apply sumBudget_mono base _ _ le_rfl
      · intro z
        dsimp only [f]
        split_ifs
        · exact mul_nonneg (Poly.worth pos _).le (mul_nonneg (M ⟨i,z⟩).sound.le (Real.exp_pos _).le)
        · exact le_rfl
      · intro z
        dsimp only [f]
        rw [located,height owner site X rooted]
        simp only [Poly.toll,Census.fire,prod_singleton]
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (pos _).le ((oldPay i).1 z)
    exact sumBudget_sigma each (budget_finite (fun i=>budget_nonneg (each i)) le_rfl)
  · intro z
    have oldSize:=(earned z.1).purchases.usable z.2
    refine ⟨oldSize.1,?_⟩
    change (old z).lamp.toll=∑v∈({owner z.1}:Finset (Fin load)),grades v
    simpa [hmode,Census.fire] using oldSize.2

end YM.Integration.WilsonGeneralArityBlockRoster
