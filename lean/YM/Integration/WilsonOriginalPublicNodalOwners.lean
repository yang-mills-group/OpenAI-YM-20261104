import YM.Integration.WilsonOriginalPublicNodalCash

/-! The occupied physical basis column of each submitted socket at its true
root. Its native planting pole is exactly that column's engineering grade. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 900000
namespace YM.Integration.WilsonOriginalPublicNodalOwners
open Finset Lattice Wilson RG Source Labels Pert.Asymptotics Laurent
open PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2
open ActualRunPhysicalPages
open WilsonThermometerDeclaredSeeds (Choice entry)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonReceivedCanonicalVerseBasis (dose)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonOriginalPublicNodalCash (axis)
open WilsonOriginalPublicNodalCanonical (request)
open WilsonOriginalPublicNodalFibre (change complete)
open WilsonOriginalPublicTrialFigure (amount)
open WilsonPositionProgramReportedField (entire)
open WilsonOriginalStarSceneWords (pole)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}[LinearOrder I](d:I→ℕ)
    {N p K:ℕ}(live:K≤N)(w:(j:I)→R.family.label (d j))
local notation "F" j:max => R.family.labels.level (d j)
local notation "g" => regulatorRun R.family N p K
local notation "V" => (fun j=>entire R (d j) K (N,p) (w j))

def owner (j:I):Choice R d j→(F j).Index
  | .inl _=>0
  | .inr x=>x.1

def home (S:Finset I)(c:Selection R d S):Columns R (fun j:S=>d j):=fun j=>owner R d j (c j)

omit [LinearOrder I] in
theorem rank (j:I)(c:Choice R d j):((F j).grades (owner R d j c)).2=pole R d (entry R d j c):=by
  rcases c with u|v
  · cases u;exact congrArg Prod.snd (F j).zero_degree
  · rfl

omit [LinearOrder I] in
theorem local_price (v v':(j:I)→R.family.label (d j))(j:I)(c:Choice R d j)(same:v j=v' j):
    dose R d N p K v j c=dose R d N p K v' j c:=by
  rcases c with u|x
  · cases u;exact congrFun same 0
  · change WilsonOriginalStarLaurentWallet.coefficient R (d j) _ _ ((F j).core (v j)) x=_
    rw [same]
    rfl

omit [LinearOrder I] in
theorem vacant (b:Columns R d)(j:I)(c:Choice R d j)(miss:b j≠owner R d j c):
    dose R d N p K (request R d b (N:=N) (p:=p) (K:=K)) j c=0:=by
  rcases c with u|x
  · cases u
    change b j≠0 at miss
    change _ * (Pi.single (b j) 1:(F j).Coeff) 0=0
    rw [Pi.single_eq_of_ne (Ne.symm miss),mul_zero]
  · change b j≠x.1 at miss
    change _*((F j).core (request R d b (N:=N) (p:=p) (K:=K) j)) x.1*_=0
    have gone:((F j).core (request R d b (N:=N) (p:=p) (K:=K) j)) x.1=0:=by
      by_cases u:x.1=0
      · simp [Frame.core,Function.update,u]
      · change Function.update ((F j).scaled _ (Pi.single (b j) 1)) 0 0 x.1=0
        rw [Function.update_of_ne u,Frame.scaled_apply,Pi.single_eq_of_ne (Ne.symm miss),mul_zero]
    rw [gone,mul_zero,zero_mul]

include live in
theorem chosen (b:Columns R d)(j:I)(c:Choice R d j)(own:b j=owner R d j c):
    amount R d g V j (b j)*dose R d N p K (request R d b (N:=N) (p:=p) (K:=K)) j c=
      dose R d N p K w j c:=by
  classical
  rw [←WilsonOriginalPublicNodalCash.original R d (p:=p) live w j c]
  rw [sum_eq_single (b j)]
  · congr 1
    apply local_price
    simp [request,axis]
  · intro k _ different
    apply mul_eq_zero_of_right
    apply vacant
    simpa [axis,←own] using different
  · simp

omit [LinearOrder I] in
theorem depth (S:Finset I)(c:Selection R d S):
    Kick.depthF univ (fun j:S=>d j) (home R d S c)=∑j:S,pole R d (entry R d j (c j)):=by
  apply sum_congr rfl
  intro j _
  exact rank R d j (c j)

omit [LinearOrder I] in
theorem clock (S:Finset I)(c:Selection R d S):
    change R d (N:=N) (p:=p) (K:=K) 1 S c=((g:ℂ)^Kick.depthF univ (fun j:S=>d j) (home R d S c))⁻¹:=by
  simp only [change,WilsonOriginalPublicNodalStencils.retime,Complex.ofReal_one,one_pow,one_mul,
    zpow_neg,zpow_natCast,prod_inv_distrib,prod_pow_eq_pow_sum,depth]

theorem other (S:Finset I)(b:Columns R (fun j:S=>d j))(c:Selection R d S)(miss:b≠home R d S c):
    weight R d N p K (request R d (complete R d S b) (N:=N) (p:=p) (K:=K)) S c=0:=by
  classical
  obtain ⟨j,wrong⟩:=Function.ne_iff.mp miss
  apply Finset.prod_eq_zero (mem_univ j)
  apply vacant
  simpa [complete,home] using wrong

include live in
theorem received (S:Finset I)(c:Selection R d S):
    WilsonOriginalPublicTrialFigure.weight R (fun j:S=>d j) g (fun j:S=>V j) (home R d S c)*
      weight R d N p K (request R d (complete R d S (home R d S c)) (N:=N) (p:=p) (K:=K)) S c=
      weight R d N p K w S c:=by
  unfold WilsonOriginalPublicTrialFigure.weight WilsonReceivedCanonicalVersePortfolio.weight
  rw [←prod_mul_distrib]
  apply prod_congr rfl
  intro j _
  have meet:complete R d S (home R d S c) j.val=owner R d j (c j):=by simp [complete,home]
  have check:=chosen R d (p:=p) live w (complete R d S (home R d S c)) j (c j) meet
  rw [meet] at check
  exact check

end YM.Integration.WilsonOriginalPublicNodalOwners
end
