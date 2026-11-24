import YM.Integration.WilsonPositionProgramTrialHomeFaces
import YM.Integration.WilsonIndependentMatchedRosterRose

/-! The seven physical (6,4,4) faces with the same seated sources on both complete vacuum histories. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialRoseHome
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace WilsonCoeffUV
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard
open WilsonIndependentMatchedRosterRose (grade seatsFor address)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonPositionProgramTrialHomeFaces (Booked)
open scoped BigOperators Topology Classical
variable {G:Gauge}{D k u e:ℕ}
abbrev Face:={s:Finset (Fin 3) // s.Nonempty}
def size (S:Face):ℕ:=(seatsFor S.val S.property).val
def leg (S:Face):Fin (size S+1)→Fin 3:=address S.val S.property
lemma full (S:Face):Set.range (leg S)=(S.val:Set (Fin 3)):=
  WilsonIndependentMatchedRosterRose.enrolled S.val S.property
lemma seven:Fintype.card Face=7:=by decide

theorem capacity (fit:6<D)(S:Face):
    capP (deck (G:=G) (grade ∘ leg S) (fun _=>D)
      (fun i=>(Nat.le_of_lt_succ (WilsonPositionThermometerGradedSource.grade (leg S i)).isLt).trans_lt fit)) ≤ 14:=by
  let f:Fin (size S+1)↪Fin 3:=(address S.val S.property).toEmbedding
  change (∑i:Fin (size S+1),grade (f i))≤14
  calc
    _=∑i∈univ.map f,grade i:=by simp
    _≤∑i:Fin 3,grade i:=sum_le_univ_sum_of_nonneg fun _=>Nat.zero_le _
    _=14:=by rw [Fin.sum_univ_three];rfl

theorem original (R:Run G)(W:Initialize G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)
    (funded:FundedMarkedCoverRows.prices v R.kit)(fit:6<D)(rails:Rails 6 k u e)
    (own:∀i,Rails (grade i) k u e)(seats:14≤k)(kind:Fin 3→Bool):
    let admit i:grade i<D:=(Nat.le_of_lt_succ (WilsonPositionThermometerGradedSource.grade i).isLt).trans_lt fit
    ∃α:∀i,Alma (R.family.labels.level (grade i))→ℝ,(∀i s,0≤α i s) ∧
    ∃Z B:Fin 3→Credit,∀ᶠ floor:ℕ in atTop,
      Booked R W grade (fun _=>D) admit kind own size leg α Z B floor:=by
  intro admit
  exact WilsonPositionProgramTrialHomeFaces.original R W simple v funded fit rails grade (fun _=>D)
    admit kind own size leg (fun S=>(capacity (G:=G) fit S).trans seats)

end YM.Integration.WilsonPositionProgramTrialRoseHome
end
