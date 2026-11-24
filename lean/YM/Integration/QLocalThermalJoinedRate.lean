import YM.Integration.QLocalMarkedJoinedWeight
import YM.Integration.QLocalThermalJoinedInvoice

/-! Charge the gained full signed forcing on the real joined inventory.
The incoming marked spectators and the unmarked K appear in the same
native per-site invoice. The tariff is fixed before every independent
test and every background field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalThermalJoinedRate
open Function Finset Lattice RG Wilson Marker Overlay Extra.Histories Planned.GuardedAtom
open RG3.Script.Picnic LocalComparison Comparison.Density.RenderM
open MergeProof.Accent Push.AbsoluteSums ActualWilsonJoinedCofactor ActualWilsonDirtyPartners
open QLocalThermalPacketDivision QLocalThermalJoinedSource
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V]
    {D:V→ ComparisonDensity.Address.Orbit} {Γ:Census V} {Q:Rep G n}
    (P:MarkedPackets D G n Γ) {p:BudgetPoint} {a:V→Support n}
    {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width budget:ℝ} {off cov:ℕ}

def charge (p:BudgetPoint) (off:ℕ) (budget:ℝ) :=
  (Fintype.card Γ.Mode:ℝ)*(2/(3*p.supportExponent))*blockSites p.B*
    ((2:ℝ)^P.rankCap*Real.exp (4*p.supportExponent*(off:ℝ))*budget)

def measured (A:TestSpace D→Bands Γ Q) (i:ℕ) (z:IndependentTests D×Config G n) :=
  (A (testInclusion D z.1)).each i z.2

theorem coupon {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V]
    {D:V→ ComparisonDensity.Address.Orbit} {Γ:Census V} {Q:Rep G n}
    (P:MarkedPackets D G n Γ) {p:BudgetPoint} {a:V→Support n}
    {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width budget:ℝ} {off cov:ℕ}
    (K:Guard.Keeper Q.p Q.activities) (H:P.Paid p a region w g width budget off cov)
    (s:Γ.Mode) (active:s≠Γ.quiet) (c:ℂ) (hc:‖c‖≤1) (A:TestSpace D→Bands Γ Q) {u:ℝ}
    (old:Towed w (ActualWilsonPacketSplit.scopes Q) (measured A) p.B p.supportExponent u)
    (small:u*blockSites p.B≤(3*p.supportExponent)/2) :
    Nonempty (QLocalMarkedJoinedWeight.Coupon p (fun i (z:IndependentTests D×Config G n)=>
      QLocalMarkedJoinedLinear.addition (Y:=plot P) K (A (testInclusion D z.1)) s
        (row P Q.p g c s (testInclusion D z.1)) i z.2) w Q
      ((2/(3*p.supportExponent))*(u*blockSites p.B)*
        ((2:ℝ)^P.rankCap*Real.exp (4*p.supportExponent*(off:ℝ))*budget))) := by
  obtain ⟨b,unit,money⟩:=QLocalThermalTokenTariff.partners P H (ActualWilsonPacketSplit.scopes Q) (measured A) old small s active
  exact QLocalMarkedJoinedWeight.weights H.positive p K (fun x=>A (testInclusion D x)) s
    (fun x=>row P Q.p g c s (testInclusion D x)) (QLocalThermalTokenTariff.stem P s w g) b _
    (QLocalThermalTokenTariff.charged P H s) unit (QLocalThermalTokenTariff.field P H Q.p c hc s) money

theorem one (K:Guard.Keeper Q.p Q.activities) (H:P.Paid p a region w g width budget off cov)
    (s:Γ.Mode) (active:s≠Γ.quiet) (c:ℂ) (hc:‖c‖≤1) (A:TestSpace D→Bands Γ Q) {u:ℝ}
    (old:Towed w (ActualWilsonPacketSplit.scopes Q) (measured A) p.B p.supportExponent u)
    (small:u*blockSites p.B≤(3*p.supportExponent)/2) :
    Towed w (ActualWilsonPacketSplit.scopes Q) (fun i (z:IndependentTests D×Config G n)=>
      QLocalMarkedJoinedLinear.addition (Y:=plot P) K (A (testInclusion D z.1)) s
        (row P Q.p g c s (testInclusion D z.1)) i z.2) p.B p.supportExponent (u*charge P p off budget) := by
  obtain ⟨value⟩:=coupon P K H s active c hc A old small
  have bill:=QLocalMarkedJoinedWeight.Coupon.towed H.positive p _ value
  convert bill using 1
  unfold charge
  ring

theorem relax {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {Q:Rep G n} {p:BudgetPoint} {w:V→ℝ}
    {X:Type*} (L:ℕ→X→Poly Γ) {u d:ℝ}
    (stamp:Towed w (ActualWilsonPacketSplit.scopes Q) L p.B p.supportExponent u) (amount:u≤d) :
    Towed w (ActualWilsonPacketSplit.scopes Q) L p.B p.supportExponent d := by
  obtain ⟨m,ss,hit,prices⟩:=stamp
  exact ⟨m,ss,fun x=>budget_loosen (hit x) amount,prices⟩

theorem physical (K:Guard.Keeper Q.p Q.activities) (H:P.Paid p a region w g width budget off cov)
    {o:V→Site n} (T:Taste (IndependentTests D) o Q Γ) {d u κ:ℝ}
    (forced:LocalComparison.Global.ForcedBudget p T w d u) (marks:∀i j,(T.menu.marks i j).val.Nonempty)
    (hK:Q.activities.KBound p κ) (s:Γ.Mode) (hs:s≠Γ.quiet) (c:ℂ) (hc:‖c‖≤1)
    (small:(κ+(Fintype.card V:ℝ)*(d*u))*blockSites p.B≤(3*p.supportExponent)/2) :
    Towed w (ActualWilsonPacketSplit.scopes Q) (fun i (z:IndependentTests D×Config G n)=>
      QLocalMarkedJoinedLinear.addition (Y:=plot P) K (T.menu.terms z.1) s
        (row P Q.p g c s (testInclusion D z.1)) i z.2) p.B p.supportExponent
      ((κ+(Fintype.card V:ℝ)*(d*u))*charge P p off budget) := by
  let F i (z:IndependentTests D×Config G n):=(T.menu.terms z.1).each i z.2
  have prior:=QLocalForcedTestForest.rows p T forced H.positive marks hK
  obtain ⟨b,unit,money⟩:=QLocalThermalTokenTariff.partners P H (ActualWilsonPacketSplit.scopes Q) F prior small s hs
  have bill:=QLocalMarkedJoinedWeight.transferred H.positive p K T.menu.terms s
    (fun x=>row P Q.p g c s (testInclusion D x)) (QLocalThermalTokenTariff.stem P s w g) b _
    (QLocalThermalTokenTariff.charged P H s) unit (QLocalThermalTokenTariff.field P H Q.p c hc s) money
  convert bill using 1
  unfold charge
  ring

private theorem sumBudgetAdd {I : Type*} {f g : I→ℝ} {a b : ℝ}
    (hf : SumBudget f a) (hg : SumBudget g b) : SumBudget (fun i => f i+g i) (a+b) := by
  refine ⟨fun i=>add_nonneg (hf.1 i) (hg.1 i),hf.2.1.add hg.2.1,?_⟩
  rw [hf.2.1.tsum_add hg.2.1]
  exact add_le_add hf.2.2 hg.2.2

theorem plus {n:Side} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {p:BudgetPoint} {w:V→ℝ}
    {X:Type*} (S:ℕ→Support n) {L M:ℕ→X→Poly Γ} {a b:ℝ}
    (left:Towed w S L p.B p.supportExponent a) (right:Towed w S M p.B p.supportExponent b) :
    Towed w S (fun i x=>L i x+M i x) p.B p.supportExponent (a+b) := by
  obtain ⟨c,cs,ca,cl⟩:=left
  obtain ⟨d,ds,da,dl⟩:=right
  refine ⟨fun i=>c i+d i,cs.add ds,?_,?_⟩
  · intro x
    convert sumBudgetAdd (ca x) (da x) using 1
    funext i
    split_ifs <;> ring
  · intro i
    obtain ⟨l,lp,lv,lb⟩:=cl i
    obtain ⟨r,rp,rv,rb⟩:=dl i
    refine ⟨fun s=>l s+r s,fun s=>add_nonneg (lp s) (rp s),?_,?_⟩
    · intro z s
      exact (norm_add_le ..).trans (add_le_add (lv z s) (rv z s))
    · simpa only [Push.GridApprox.Nil.wordsPrice,mul_add,Finset.sum_add_distrib] using add_le_add lb rb

end YM.Integration.QLocalThermalJoinedRate
