import YM.Integration.WilsonConditionalTaylorBulkPass
import YM.Integration.WilsonConditionalTaylorBulkClock
import YM.Integration.WilsonConditionalTaylorSceneReset

/-! The finite torus Wilson recursion on the genuine funded original:
actual plaquette seed, genuine step, signed measured scalar, and booked
coupling at every age. The cutoff horizon and the physical Side scale
are fixed before the test. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorBulkHistory
open Function PowerSeries Lattice RG Wilson Tree Stationary Push.Uniform Bloch
open FormalBulk08 FormalBulk08.Jets Flat Reef Mesa Lava Shore Lotus Wine Bank Orb
open Next.Free PhysicalNext.Repeat.Legato WilsonConditionalTaylorBulkShape
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (u : G.ColorIndex)
variable (wood : ∀ j,Lodge (R.family.path.levels.clock.op j 0).patch)
variable (tags : ∀ j n, (primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)

def raw (N j : ℕ) (U : (n:Side)→Pap (wire G n)) (n : Side) : Pap (wire G n) :=
  let V:=R.family.path.levels
  let P:=destination V N j
  Reef.landed P R.metals.O (V.blocks j 0).branches (wood j) n (tags j n) (U (n*P.L))

def reset (N j : ℕ) (n : Side) (Z : Pap (wire G n)) : Pap (wire G n) :=
  let H:=WilsonConditionalTaylorBulkClock.field (MSbar.Lis.sun G u)
    (R.alloy.B.kin.path N j) (R.family.path.levels.params j).clip Z
  Wine.canter (bookH H) (bookU H) _ Z

def levels (N : ℕ) : ℕ → ℕ → (n:Side)→Pap (wire G n)
  | 0,_ => fun n=>Reef.seed G n
  | d+1,j => fun n=>reset R u N j n (raw R wood tags N j (levels N d (j+1)) n)

def course (N j : ℕ) := levels R u wood tags N (N-j) j

theorem ultraviolet (N : ℕ) (n : Side) : course R u wood tags N N n=Reef.seed G n := by
  rw [course,Nat.sub_self,levels]

theorem next (N j : ℕ) (hi : j<N) : course R u wood tags N j =
    fun n=>reset R u N j n (raw R wood tags N j (course R u wood tags N (j+1)) n):=by
  unfold course
  rw [show N-j=N-(j+1)+1 by omega,levels]

private theorem bareShape (n : Side) : Ranks (Reef.seed G n):=by
  intro e r _ present
  by_contra! fail
  have diff : r ≠ 2+e:=by omega
  apply present
  rw [rancho,marble_eq_zero_iff,Reef.seed,map_neg,after_one,map_neg,
    MvPolynomial.homogeneousComponent_of_mem (paste_grade ..),if_neg diff,neg_zero]

theorem admitted (N j : ℕ) (age : j≤N) : ∀ n:Side,
    coeff 0 (course R u wood tags N j n)=crunch (kernelP G R.family.path.levels.clock.kernel.penalty
      (location R.family.path.levels N j) n) ∧ Ranks (course R u wood tags N j n) ∧ Civic (course R u wood tags N j n) :=by
  let V:=R.family.path.levels
  let K:=RunFormalChain.fromRun R
  induction age using Nat.decreasingInduction with
  | self =>
    intro n
    rw [ultraviolet,loc_top]
    exact ⟨seed_first V.clock.kernel.penalty V.clock.kernel.penalty_pos _ (V.clock.adm _),bareShape _,seed_ward⟩
  | of_succ j late ih =>
    intro n
    let P:=destination V N j
    let U:=course R u wood tags N (j+1)
    let Z:=raw R wood tags N j U n
    have pre := ih (n*P.L)
    have head : coeff 0 Z=crunch (kernelP G V.clock.kernel.penalty P.land n) :=
      Reef.landed_cost P R.metals.O (V.blocks j 0).branches (wood j) n (tags j n) _ pre.1 K.receipt (V.clock.adm j)
    have r : Ranks Z := WilsonConditionalTaylorBulkShape.output P (wood j) R.metals.O (V.blocks j 0).branches n (tags j n) _ K.receipt (V.clock.adm j) pre.2.1 pre.1
    have c : Civic Z := Reef.landed_ward P R.metals.O (V.blocks j 0).branches (wood j) n (tags j n) _ pre.1 K.receipt (V.clock.adm j) pre.2.2
    have bought:=WilsonConditionalTaylorBulkClock.actual (MSbar.Lis.sun G u) (R.alloy.B.kin.path N j)
      (V.params j).clip Z r (by rw [head];exact kinetic_grade _) c
    rw [next R u wood tags N j late,loc_land _ N j late]
    exact ⟨bought.1.trans head,bought.2⟩

end YM.Integration.WilsonConditionalTaylorBulkHistory

