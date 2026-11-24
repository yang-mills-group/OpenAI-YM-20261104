import YM.Integration.WilsonOriginalConditionalCovarianceReturn

/-! Signed first-join contributions at every original date; the two full
conditional means are still read together on the physical older law. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalCovarianceDatedPassage
open MeasureTheory Lattice RG Wilson Source Labels OPE.Therm
open PhysicalNext.Repeat.Legato WilsonOriginalConditionalCovarianceReturn
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N p K:ℕ}
local notation "space" j:max => Config G (R.family.side j p)
local notation "ν" j:max => scene R.family.path N p j

def port (N:ℕ)(F:space K→ℂ)(j:ℕ):space j→ℂ:=
  if h:j≤K then actualTransport R.family (N:=N) F h else 0

def level (N:ℕ)(F H:space K→ℂ)(j:ℕ):ℂ:=
  covariance (scene R.family.path N p j) (port R N F j) (port R N H j)

def joint (N:ℕ)(F H:space K→ℂ)(j:ℕ):ℂ:=
  ∫V,actualTransport R.family (N:=N)
    (fun U=>port R N F (j+1) U*port R N H (j+1) U) (Nat.le_succ j) V-
    port R N F j V*port R N H j V ∂scene R.family.path N p j

theorem edge {F H:space K→ℂ}{A B:ℝ}(a:Billed R A F)(b:Billed R B H)
    (cut:K≤N){j:ℕ}(before:j+1≤K):
    level R N F H (j+1)=level R N F H j+joint R N F H j:=by
  have prior:j≤K:=(Nat.le_succ j).trans before
  have e:=WilsonOriginalConditionalCovarianceReturn.original R (carry R a cut before)
    (carry R b cut before) (before.trans cut) (Nat.le_succ j)
  dsimp only at e
  rw [actualTransport_tower R.family R.makes cut F before (Nat.le_succ j),
      actualTransport_tower R.family R.makes cut H before (Nat.le_succ j)] at e
  simpa only [level,joint,port,dif_pos before,dif_pos prior] using e.trans (add_comm _ _)

/-- Every edge occurs once, with its true earlier scene as the integration measure. -/
theorem original {F H:space K→ℂ}{A B:ℝ}(a:Billed R A F)(b:Billed R B H)
    (cut:K≤N){u:ℕ}(old:u≤K):
    covariance (ν K) F H=level R N F H u+
      ∑j∈Finset.range (K-u),joint R N F H (u+j):=by
  have chain (s:ℕ)(inside:u+s≤K):level R N F H (u+s)=level R N F H u+
        ∑j∈Finset.range s,joint R N F H (u+j):=by
    induction s with
    | zero => simp
    | succ s ih =>
      rw [Finset.sum_range_succ,←add_assoc (level R N F H u) _ _,←ih (by omega)]
      exact edge R a b cut inside
  have h:u+(K-u)=K:=by omega
  have full:=chain (K-u) (le_of_eq h)
  rw [h] at full
  simpa only [level,port,dif_pos (le_refl K),actualTransport_base R.family R.makes cut] using full
end YM.Integration.WilsonOriginalCovarianceDatedPassage
end
