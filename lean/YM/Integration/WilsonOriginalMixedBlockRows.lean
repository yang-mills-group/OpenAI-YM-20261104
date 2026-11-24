import YM.Integration.WilsonGeneralArityBlockRoster

/-! Mount a previously connected deposited block on its original occupied names.
The physical lag, field atom and root persist. The wallet tests the product of
the individual source amplitudes on this same occupied face. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMixedBlockRows
open Function Finset Lattice Laurent RG Wilson Marker Multi Gauge
open Push Push.AbsoluteSums Push.Local Paths Animals ConnectedActivityE6 QuadraticLocal
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink QuadraticLocal.Affinity
open WilsonRegisteredPairUnaryWallet
open scoped Classical BigOperators

def room (V:Type):V→Set ℂ:=fun _=>disk ()
variable {V:Type} [Fintype V] [DecidableEq V]
local notation "J" => Stock.census V
local notation "W" => Stock.census Unit
def project (s:(J).Mode) (x:Wallet (room V)):Wallet disk:=fun _=>⟨∏v∈s.val,(x v).val,by
  change ‖∏v∈s.val,(x v).val‖ ≤ 1
  rw [norm_prod]
  exact prod_le_one (fun v _=>norm_nonneg _) fun v _=>(x v).property⟩

variable {G:Gauge} {n:Side} {I:Type} {O:I→Type} {P:Passport n V} (B:I→Earn.Binder P (Stock.census V))
  (X:(i:I)→O i→Earn.Row (Passport.point (fun _:Unit=>(B i).center)) W G (Wallet disk))
local notation "old" z:max => X (z).1 (z).2
def mounted (z:(i:I)×O i):Earn.Row P (Stock.census V) G (Wallet (room V)) where
  binder:=B z.1
  lamp:=(old z).lamp
  atom:=(old z).atom
  lawful:=(old z).lawful
  clear:=(old z).clear
  salary:=(old z).salary
  sound:=(old z).sound
  paint x:=(old z).paint (project (B z.1).mode x)
  rank:=(old z).rank

local notation "M" => mounted B X
theorem located (z:(i:I)×O i):(M z).binder=B z.1:=rfl
theorem individual (z:(i:I)×O i)(t:Wallet (room V))(g:ℝ)(U:Config G n):
    (M z).nominal g t U=(old z).nominal g (project (B z.1).mode t) U:=rfl

variable (rooted:∀(i:I)(z:O i),(X i z).binder=WilsonOlderFreshGraphPointWallet.point (B i).center)
  (linear:∀i z,∃c:ℂ,∀x:Wallet disk,(X i z).paint x=c*WilsonThermometerRegisteredCapturedSector.amplitude disk x)

include rooted in
theorem height (z:(i:I)×O i)(σ:ℝ):(M z).height σ=
    Real.exp (σ*(B z.1).length)*(old z).height σ:=by
  change (old z).salary*Real.exp (σ*((((B z.1).length+(old z).atom.length:ℕ):ℝ)))=
    _*((old z).salary*Real.exp (σ*((((old z).binder.length+(old z).atom.length:ℕ):ℝ))))
  rw [rooted]
  simp only [WilsonOlderFreshGraphPointWallet.point,WilsonOriginalStarSceneRows.length,
    Nat.zero_add,Nat.cast_add,mul_add,Real.exp_add]
  ring

local notation "zeros" => (fun _:V=>(⊥:Submodule ℝ ℂ))
include linear in
theorem tested:Tableau zeros (room V) M:=by
  constructor
  intro z
  obtain ⟨c,paint⟩:=linear z.1 z.2
  let s:=(B z.1).mode.val
  have funEq:(M z).paint=(fun t=>(∏v∈s,(t v).val)*c):=funext fun t=>(paint _).trans (mul_comm ..)
  rw [funEq]
  change Attn zeros (room V) s _
  refine ⟨?_,?_,?_⟩
  · intro x y keep
    exact congrArg (fun z=>z*c) (prod_congr rfl fun j hj=>congrArg Subtype.val (keep j hj))
  · intro j hj t x y z a b rel
    let k:=(∏ v∈s.erase j,(t v).val)*c
    have updated (p:room V j):(∏v∈s,((Function.update t j p) v).val)*c=p.val*k:=by
      rw [← Finset.mul_prod_erase _ _ hj,Function.update_self,mul_assoc]
      congr 2
      exact prod_congr rfl fun v hv=>congrArg Subtype.val (Function.update_of_ne (ne_of_mem_erase hv) p t)
    rw [updated,updated,updated,rel]
    simp only [Complex.real_smul,add_mul]
    ring
  · intro j hj t h
    have zero:(t j).val=0:=(Submodule.mem_bot ℝ).mp h
    rw [← Finset.mul_prod_erase _ _ hj,zero,zero_mul,zero_mul]

end YM.Integration.WilsonOriginalMixedBlockRows
end
