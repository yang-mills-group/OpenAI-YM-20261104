import YM.Integration.WilsonOriginalReceivedFiniteChain
import YM.Integration.WilsonOlderFreshIssuedIntake
import YM.MergeProof.Pitch

/-! The measured kinetic restamp on every group configuration, including its signed defect. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderFreshWordReversion
open Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Rebirth AllOrder
open Comparison.RG02 Stationary AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit
open QuadraticLocal.Sunrise QuadraticLocal.Poetry Next.Scheduling AllOrder.Wheel Laurent
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V ι W : Type} [DecidableEq V] {C : Census V}
  {p : Earn.Passport n V} (M : ι → Row p C G W)

/-- The salary applies before selecting a test.  Every charged Laurent lag is evaluated
at the actual nonzero coupling, and every original path is read on the submitted field. -/
theorem funded {a t w b q u k} (salary : Scene.Armada M w t a b q k u) (ha : 0<a)
    (x : W) (layout : Layout G) (tape : Finset Age) {g : ℝ} (hg : g≠0) (U : Config G n) :
    HasSum (fun j=>Spill.raw M g x j U)
      (Integral.markedLog g U (Air.craft M (fun j=>(M j).paint x) t layout tape)) := by
  letI : Fintype V := Fintype.ofInjective C.fire (fun a b h => (C.fire_inj a b).mp h)
  let ink := fun j=>(M j).paint x
  have staff := Air.license M ink t w salary ha (fun j=>salary.honor j x)
  apply (Air.liftPassport M ink t staff layout tape g hg U).congr_fun
  intro i
  rfl

theorem quiet (x : W) (g : ℝ) (U : Config G n) :
    (Spill.Foundry.uncut M g x U).part C.quiet=0 := by
  unfold Spill.Foundry.uncut
  by_cases h : Summable (fun j=>Spill.raw M g x j U)
  · rw [Poly.share h]
    calc
      _ = ∑' _ : ι, (0 : ℂ) := tsum_congr fun j=>
        (Poly.part_send ..).trans (if_neg (M j).binder.live.symm)
      _ = 0 := tsum_zero
  rw [tsum_eq_zero_of_not_summable h]
  rfl

theorem singleton [Fintype V] (x : W) (g : ℝ) (U : Config G n) (v : V) (c : ℂ) :
    (c • Poly.pass (Spill.Foundry.uncut M g x U)).part (C.fire v) =
      c*(Spill.Foundry.uncut M g x U).part (C.fire v) := by
  rw [Poly.part_smul,MergeProof.Accent.whisper _ _ (quiet M x g U)]

theorem same {p' : Earn.Passport n V} {ι' : Type} (M' : ι' → Row p' C G W)
    (passport : p=p') (names : ι=ι') (equal : HEq M M') :
    Spill.Foundry.uncut M=Spill.Foundry.uncut M' := by
  subst p'
  subst ι'
  cases eq_of_heq equal
  rfl

variable (B : BudgetPoint) (coin : Pace.Coin) (zero : coin 0=0) (d q : ℕ)
  {g t : ℝ} (hg : g≠0) (ht : t≠0) (x : W) (U : Config G n)
local notation "stamp" => Mutation.stamp M coin zero d q
local notation "debt" => Mutation.mend M B coin zero d q g t
local notation "diff" => (fun j=>Poly.send (M j).mode ((debt).nominal x j U))

include hg ht in
/-- Absolute summation of each physical group-word family preserves every edge of the
upper word's finite kinetic restamp.  The signed defect uses the original row's address. -/
theorem reversion (incoming : Summable (fun j=>Spill.raw M g x j U))
    (outgoing : Summable (fun j=>Spill.raw stamp t x j U)) :
    HasSum diff (Spill.Foundry.uncut M g x U-Spill.Foundry.uncut stamp t x U) := by
  let F := fun j : Mutation.Names M q => Spill.raw stamp t x j U
  have groups : HasSum (fun j=>∑ z:Mutation.ways M q j,F ⟨j,z⟩) (Spill.Foundry.uncut stamp t x U) :=
    outgoing.hasSum.sigma (f:=F) (fun j=>hasSum_fintype _)
  apply (incoming.hasSum.sub groups).congr_fun
  intro j
  ext mode
  have h := Mutation.letters M B coin zero d q g t hg ht j x U
  change (Poly.send (M j).mode _).part mode=(Spill.raw M g x j U - ∑ z:Mutation.ways M q j,F ⟨j,z⟩).part mode
  simp only [Poly.part_send,Extra.Trajectories.part_sub,Poly.part_sum,Spill.raw,F]
  change (if mode=(M j).mode then _ else 0)=
    (if mode=(M j).mode then _ else 0)-∑ z:Mutation.ways M q j,if mode=(M j).mode then _ else 0
  by_cases present : mode=(M j).mode
  · simp only [if_pos present]
    exact eq_sub_of_add_eq' h.symm
  simp only [if_neg present,sum_const_zero,sub_zero]

end YM.Integration.WilsonOlderFreshWordReversion
