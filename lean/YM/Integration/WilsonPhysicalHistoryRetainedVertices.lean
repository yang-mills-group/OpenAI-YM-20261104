import YM.Integration.WilsonPhysicalHistoryRetainedMayer
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Batch

/-! The exact unselected companions of the omitted activity in a genuine
finite Mayer molecule, including every flag and previously booked forced bag. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open ConnectedActivityE6 ConnectedActivityE6.Coat
open Bloch Laurent Push Push.AbsoluteSums Precision Exterior Shell Channel
open PhysicalNext.Repeat.Legato
open scoped Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

def regularHead (S : StepData c f) (i : ℕ) : Head S := .inr (.inr (.inl (.inl (.inl i))))

private theorem same_storm (X : Coat T F) (P : Rep G f) (K : Activities G f)
    (hf : K.forced=P.activities.forced) (u : Directions G f) (W a : ℝ) (l : Finset ℕ) :
    X.detect u W a P l=X.detect u W a {P with activities:=K} l := by
  unfold Coat.detect Coat.mayor Coat.rawStorm Contract.charges Contract.covered
  simp only [hf]

private theorem same_pack (X : Coat T F) (P : Rep G f) (K : Activities G f)
    (hf : K.forced=P.activities.forced) (C : ChartRatio G) (l : Finset ℕ)
    (W a : ℝ) (A : Stores S) (u : Directions G f) :
    X.Pack P C l W a A u=X.Pack {P with activities:=K} C l W a A u := by
  unfold Coat.Pack Coat.steam Coat.steamLog Contract.order Contract.charges Contract.covered
  simp only [hf]

private theorem same_bag (X : Coat T F) (P : Rep G f) (K : Activities G f)
    (hf : K.forced=P.activities.forced) (hc : K.K=P.activities.K) (a : ℝ) (u : Directions G f) (i : ℕ) :
    X.bag P a u i=X.bag {P with activities:=K} a u i := by
  simp [Coat.bag,Raw.forcedFoot,hf,hc]

private theorem partners (X : Coat T F) (P Q : Rep G f)
    (same : Q={P with activities:=Q.activities})
    (hf : Q.activities.forced=P.activities.forced) (hc : Q.activities.K=P.activities.K)
    (C : ChartRatio G) (W a : ℝ) (l : Finset ℕ) (m : ℕ) (z : Air f G)
    (raised : ∀ k : LogIndex c f,(∀ i : ℕ,k≠.inl (.inl i)) →
      X.raiseAir P a C z k=X.raiseAir Q a C z k) (v : Head S)
    (away : ∀ i : ℕ,v≠regularHead S i) :
    X.vertex P C W a l m z v=X.vertex Q C W a l m z v := by
  have beta := congrArg (fun R : Rep G f=>R.beta) same
  change Q.beta=P.beta at beta
  let u:=X.liftA P.beta z
  rcases v with packet|bag|log|storm
  · simp only [Coat.vertex,Sum.elim_inl,beta]
    exact congrArg (fun f : ℝ=>if Packets.connected S m X.B packet then f else 0)
      ((same_pack X P Q.activities hf C l W a packet u).trans
        (congrArg (fun R=>X.Pack R C l W a packet u) same.symm))
  · simp only [Coat.vertex,Sum.elim_inr,Sum.elim_inl,beta]
    exact (same_bag X P Q.activities hf hc a u bag).trans
      (congrArg (fun R=>X.bag R a u bag) same.symm)
  · simp only [Coat.vertex,Sum.elim_inr,Sum.elim_inl]
    exact raised log (fun i h=>away i (congrArg (fun t : LogIndex c f=>(Sum.inr (Sum.inr (Sum.inl t)) : Head S)) h))
  · simp only [Coat.vertex,Sum.elim_inr,beta]
    exact congrFun ((same_storm X P Q.activities hf u W a l).trans
      (congrArg (fun R=>X.detect u W a R l) same.symm)) storm

theorem molecule_rows (R : Run G) {N n j d : ℕ} (hj : j<N) (A : Comparison R (p:=n) hj d) :
    let P:=R.family.path.rep N n j
    let Q:=approximation R (p:=n) hj d
    let δ:=(Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N n (j+1))^(d+1)
    ∃ b : ℕ→ℝ, (∀ x,SumBudget (fun i=>if (P.activities.reg i).site=x then
      P.p.mass (P.activities.reg i).support (b i) else 0) δ) ∧
      ∀ {c : Side} {S : StepData c (R.family.side j n)} {T : Tube G S} {F : Forest S.ratio}
        (X : Coat T F) (C : ChartRatio G) (W a : ℝ) (l : Finset ℕ) (m : ℕ)
        (z : Air (R.family.side j n) G),
        (∀ i : ℕ,δ≤1 →
          |X.vertex P C W a l m z (regularHead S i)-X.vertex Q C W a l m z (regularHead S i)| ≤
            2*(1+|X.vertex P C W a l m z (regularHead S i)|)*b i) ∧
        ∀ v : Head S,(∀ i : ℕ,v≠regularHead S i) →
          X.vertex P C W a l m z v=X.vertex Q C W a l m z v := by
  dsimp only
  obtain ⟨b,pay,_,rows⟩:=raised_rows R hj A
  obtain ⟨same,_,_,_,hf,hc,_⟩:=retained_rows R hj A
  refine ⟨b,pay,?_⟩
  intro c S T F X C W a l m z
  exact ⟨(rows X a C z).1,partners X _ _ same hf hc C W a l m z (rows X a C z).2⟩

end YM.Integration.OriginalMarkedRunAction
