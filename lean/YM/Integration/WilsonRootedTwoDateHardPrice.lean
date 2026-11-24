import YM.Integration.QLocalThermalJoinedForcedRegister
import YM.Integration.QLocalFixedJoinedPrice
import YM.Integration.WilsonRootedTwoDateHardCoupon

/-! Price a previously fixed register on the real joined hard inventory. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateHardPrice
open Function Finset Lattice RG Wilson Marker Overlay Extra.Histories Planned.GuardedAtom
open RG3.Script.Picnic LocalComparison LocalComparison.Global Comparison.Density.RenderM
open MergeProof.Accent Push.AbsoluteSums ActualWilsonJoinedCofactor ActualWilsonDirtyPartners
open QLocalThermalPacketDivision QLocalThermalJoinedSource QLocalThermalJoinedRate
open QLocalCompulsoryJoinedTape QLocalMarkedJoinedLinear QLocalMarkedJoinedCatalogue
open QLocalThermalJoinedForcedRegister WilsonLimitConstruction.FundedMarkedFieldSplit
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V] {Q:Rep G n}
    {D:V→ ComparisonDensity.Address.Orbit} {Γ:Census V} {o:V→Site n} {p:BudgetPoint}
    (P:MarkedPackets D G n Γ) {a:V→Support n} {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width budget:ℝ} {off cov:ℕ}

variable (oldD : V → ComparisonDensity.Address.Orbit)
local notation "Joint" => TestSpace oldD × TestSpace D
local notation "UnitTests" => IndependentTests oldD × IndependentTests D
local notation "incl" => WilsonRootedTwoDateHardSource.inclusion (D:=D) oldD

theorem registered (K:Guard.Keeper Q.p Q.activities) (H:P.Paid p a region w g width budget off cov) (bc:0≤budget) (hg:g≠0)
    (point:∀v,o v∈a v) (c:ℂ) (hc:‖c‖≤1) (T:Taste (Joint) o Q Γ)
    (L : QLocalFixedJoinedFamily.Fixed K T (WilsonRootedTwoDateHardSource.source (Q:=Q) P oldD H hg c))
    {κ k b:ℝ} (valid:Q.activities.ForcedFamily Q.p) (live:∀x,(T.leaf x).Active)
    (divisor:0<κ) (hK:Q.activities.KBound p k) (B:ForcedBudget p (pullback (incl) T) w κ b)
    (small:2*(k+(Fintype.card V:ℝ)*(κ*b))*blockSites p.B≤(3*p.supportExponent)/2)
    (room:2*(Fintype.card V:ℝ)*(Fintype.card Γ.Mode:ℝ)*charge P p off budget≤1) :
    Nonempty (ForcedBudget p (pullback (incl) (replace T L.book)) w κ (b+increase P p off budget κ k b)) := by
  let u:=k+(Fintype.card V:ℝ)*(κ*b)
  let fee:=charge P p off budget
  let piece:=2*u*fee/κ
  let F:=WilsonRootedTwoDateHardSource.source (Q:=Q) P oldD H hg c
  have u0:0≤u:=by
    have prior:=QLocalForcedTestForest.rows p (pullback (incl) T) B H.positive
      (fun i j=>(live ((incl) (zeroIndependentTests oldD,zeroIndependentTests D))).articles.occurs i j) hK
    exact budget_nonneg (prior.choose_spec.2.1 0)
  have fee0:0≤fee:=by
    have ex:=p.exponent_pos
    dsimp [fee,charge,blockSites]
    positivity
  have piece0:0≤piece:=by dsimp [piece]; positivity
  let Good (A:(Joint)→Bands Γ Q) (j:ℕ):=
    (∀x,(A x).origins=o ∧ (A x).Active) ∧ ∃Z:Taste (Joint) o Q Γ,
      (∀x,A x=Z.menu.terms x) ∧ Nonempty (ForcedBudget p (pullback (incl) Z) w κ (b+(j:ℝ)*piece))
  have start:Good T.menu.terms 0:=⟨fun x=>⟨T.root,(live x).articles⟩,T,fun _=>rfl,by simpa using Nonempty.intro B⟩
  have step (A:(Joint)→Bands Γ Q) (j:ℕ) (hj:j<Fintype.card Γ.Mode) (info:Good A j)
      (fin:∀x,Financed (A x)) (s:Γ.Mode) (hs:s≠Γ.quiet) :
      Good (fun x=>bands (A x) (addition (Y:=plot P) K (A x) s (F.field s x))) (j+1):=by
    obtain ⟨Z,same,⟨asset⟩⟩:=info.2
    have eq:A=Z.menu.terms:=funext same
    subst A
    let d x:=addition (Y:=plot P) K (Z.menu.terms x) s (F.field s x)
    let next:=replace Z (tape Z d)
    have all x:(bands (Z.menu.terms x) (d x)).Active:=by
      have law:=QLocalThermalJoinedLaw.charged (Q:=Q) P H o point s x.2 c
      have ok:=QLocalMarkedJoinedEligibility.issued K (Z.menu.terms x) (info.1 x).2 valid (fin x).1
        s (F.field s x) ((info.1 x).1.symm ▸ law)
      exact QLocalCompulsoryJoinedTape.active _ (info.1 x).2 _ ok
    refine ⟨fun x=>⟨(info.1 x).1,all x⟩,next,fun _=>rfl,?_⟩
    have prior:=QLocalForcedTestForest.rows p (pullback (incl) Z) asset H.positive
      (fun i j=>(info.1 ((incl) (zeroIndependentTests oldD,zeroIndependentTests D))).2.occurs i j) hK
    have amount:k+(Fintype.card V:ℝ)*(κ*(b+(j:ℝ)*piece))≤2*u:=by
      have size:(j:ℝ)≤(Fintype.card Γ.Mode:ℝ):=by exact_mod_cast hj.le
      have a:=mul_le_mul_of_nonneg_right size piece0
      have ab:=mul_le_mul_of_nonneg_left a (mul_nonneg (Nat.cast_nonneg (Fintype.card V)) divisor.le)
      have left:=mul_le_mul_of_nonneg_left room u0
      have op:piece*κ=2*u*fee:=div_mul_cancel₀ _ divisor.ne'
      let v : ℝ := Fintype.card V
      let M : ℝ := Fintype.card Γ.Mode
      calc _=u+(v*κ)*((j:ℝ)*piece) := by dsimp [u,v]; ring
           _≤u+(v*κ)*(M*piece) := add_le_add le_rfl ab
           _=u+u*(2*v*M*fee) := by
             rw [show (v*κ)*(M*piece)=v*M*(piece*κ) by ring,op]
             ring
           _≤u+u := add_le_add le_rfl (by simpa only [mul_one] using left)
           _=2*u := by ring
    obtain ⟨ticket⟩:=WilsonRootedTwoDateHardCoupon.coupon P oldD K H s hs c hc Z.menu.terms
      (relax _ (show Towed w (ActualWilsonPacketSplit.scopes Q) (WilsonRootedTwoDateHardCoupon.measured oldD Z.menu.terms) p.B p.supportExponent _ from prior) amount) small
    obtain ⟨account⟩ := QLocalMarkedJoinedForcedBudget.serial (fun x=>d ((incl) x))
      (pullback (incl) Z) H.positive divisor asset ticket
    have values (x : IndependentTests oldD × IndependentTests D) :
        (replace (pullback (incl) Z) (QLocalCompulsoryJoinedTape.tape (pullback (incl) Z) (fun y=>d ((incl) y)))).menu.terms x =
          (pullback (incl) next).menu.terms x := rfl
    have carried := follows (zeroIndependentTests oldD,zeroIndependentTests D) _ _ values account
    have money : b+(j:ℝ)*piece+(Fintype.card Γ.Mode:ℝ)*
        ((2/(3*p.supportExponent))*((2*u)*blockSites p.B)*
          ((2:ℝ)^P.rankCap*Real.exp (4*p.supportExponent*(off:ℝ))*budget))/κ = b+((j+1:ℕ):ℝ)*piece := by
      push_cast
      dsimp [piece,fee,charge]
      ring
    exact money ▸ carried
  have ledger:=L.preserves Good start step
  obtain ⟨Z,ident,⟨asset⟩⟩:=ledger.2
  have equal x:(pullback (incl) Z).menu.terms x=(pullback (incl) (replace T L.book)).menu.terms x:=
    (ident ((incl) x)).symm
  obtain ⟨bought⟩:=follows (zeroIndependentTests oldD,zeroIndependentTests D) _ _ equal asset
  have count:((Finset.univ.erase Γ.quiet).card:ℝ)≤(Fintype.card Γ.Mode:ℝ):=by
    exact_mod_cast Finset.card_le_univ (Finset.univ.erase Γ.quiet)
  have extension : ((Finset.univ.erase Γ.quiet).card:ℝ)*piece ≤ increase P p off budget κ k b :=
    (mul_le_mul_of_nonneg_right count piece0).trans_eq (by dsimp [increase,piece,u,fee]; ring)
  refine ⟨{bought with total:=?_}⟩
  intro v
  exact budget_loosen (bought.total v) (mul_le_mul_of_nonneg_left (add_le_add le_rfl extension) divisor.le)

end YM.Integration.WilsonRootedTwoDateHardPrice
end
