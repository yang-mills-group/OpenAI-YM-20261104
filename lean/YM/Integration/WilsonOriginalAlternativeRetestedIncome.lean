import YM.Integration.WilsonOriginalAlternativeRetest
import YM.Integration.WilsonOriginalReceivedPost

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeRetestedIncome
open Function Finset Set Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open WilsonOriginalAlternativeNames WilsonOriginalAlternativeRetest
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V] {X:V→Type} [∀i,AddCommGroup (X i)] [∀i,Module ℝ (X i)]
  (A:∀i,Set (X i)) (K:∀i,Submodule ℝ (X i)) (zero:∀i,0∈A i) (c:V→Port)
variable {G:Gauge} {n:Side} {P:BudgetPoint} {J:Census V} {o:V→Site n}
  {I:Type} {W:Rep G n} {pass:Passport n V} {w:V→ℝ} {a k σ b:ℝ} {B:ℕ}
local notation "t_" => submitted A zero c

def row (Z:Row pass J G (Wallet A)):Row pass J G (Wallet A):={Z with paint:=Z.paint∘t_}

variable (X₀:I→Row pass J G (Wallet A))

theorem tableau (actual:Tableau K A X₀):Tableau K A (row A zero c ∘ X₀):=
  ⟨fun i=>attentive A K zero c (actual.bill i)⟩

omit [∀i,Module ℝ (X i)] in
theorem salary {grades:V→ℕ} {k r d:ℕ} (actual:Scene.Armada X₀ w grades σ b k r d):
    Scene.Armada (row A zero c ∘ X₀) w grades σ b k r d:=
  ⟨actual.toMinistry,actual.positive,actual.suggests,⟨actual.purchases.spend,actual.purchases.usable⟩,fun i x=>actual.honor i (t_ x)⟩

omit [∀i,Module ℝ (X i)] in
theorem voter {r k st vac p:ℕ} (actual:Mentor.Cruise.Voter X₀ σ r k st vac p):
    Mentor.Cruise.Voter (row A zero c ∘ X₀) σ r k st vac p:=
  ⟨fun i=>⟨fun x=>(actual.readout i).1 (t_ x),(actual.readout i).2⟩,actual.room,actual.height,actual.tall⟩

omit [∀i,Module ℝ (X i)] in
theorem regular (E:Lamps (Wallet A) I G P o J) (actual:E.Paid w B a b):
    (E.pullback t_).Paid w B a b:=by
  obtain ⟨f,non,major,hit⟩:=actual.budget
  exact ⟨f,non,fun i x=>major i (t_ x),hit⟩

omit [∀i,Module ℝ (X i)] in
theorem hard (H:Hard (Wallet A) W.p W.activities.forced W.activities.K o J) (actual:H.Paid w B a b):
    (H.pullback t_).Paid w B a b:=by
  obtain ⟨f,major,hit⟩:=actual.wages
  exact ⟨f,fun i x=>major i (t_ x),hit⟩

theorem old (X:V→Support n) (E:Lamps (Wallet A) I G P o J) (actual:Taut X A K E):
    Taut X A K (E.pullback t_):=by
  obtain ⟨site,lesson⟩:=actual
  exact ⟨site,fun i U=>attentive A K zero c (lesson i U)⟩

theorem owner (X:V→Support n) (H:Hard (Wallet A) W.p W.activities.forced W.activities.K o J)
    (actual:Crown X A K H): Crown X A K (H.pullback t_):=by
  constructor
  intro i U
  constructor
  intro s
  have old:=(actual.lesson i U).each s
  exact ⟨attentive A K zero c old.advice,fun x=>old.announces (t_ x)⟩

theorem all_forced (X:V→Support n) (H:Hard (Wallet A) W.p W.activities.forced W.activities.K o J)
    (actual:Crown X A K H) (x:Wallet A) (i:ℕ) (U:Config G n):
    (H.pullback t_).hard x i U=Multi.dilation J (fun z=>retain (c z)) (H.hard x i U):=by
  ext s
  rw [Multi.dilation_part]
  exact printed A K zero c s ((actual.lesson i U).each s).advice x

end YM.Integration.WilsonOriginalAlternativeRetestedIncome
