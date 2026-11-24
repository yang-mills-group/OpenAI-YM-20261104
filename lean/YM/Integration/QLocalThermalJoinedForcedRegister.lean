import YM.Integration.QLocalThermalJoinedPublication
import YM.Integration.QLocalMarkedJoinedForcedBudget
import YM.Integration.QLocalMarkedJoinedLetters

/-! The fully legal, density-exact signed compulsory tape with an actual
native ForcedBudget on every one of its scalar entry addresses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalThermalJoinedForcedRegister
open Function Finset Lattice RG Wilson Marker Overlay Extra.Histories Planned.GuardedAtom
open RG3.Script.Picnic LocalComparison LocalComparison.Global Comparison.Density.RenderM
open MergeProof.Accent Push.AbsoluteSums ActualWilsonJoinedCofactor ActualWilsonDirtyPartners
open QLocalThermalPacketDivision QLocalThermalJoinedSource QLocalThermalJoinedRate
open QLocalCompulsoryJoinedTape QLocalMarkedJoinedLinear QLocalMarkedJoinedCatalogue
open WilsonLimitConstruction.FundedMarkedFieldSplit
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V] {Q:Rep G n}
    {D:V→ ComparisonDensity.Address.Orbit} {Γ:Census V} {o:V→Site n} {p:BudgetPoint}
    (P:MarkedPackets D G n Γ) {a:V→Support n} {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width budget:ℝ} {off cov:ℕ}

theorem follows {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V] {Q:Rep G n} {Γ:Census V}
    {o:V→Site n} {p:BudgetPoint} {w:V→ℝ} {X:Type*} (z:X) (T R:Taste X o Q Γ) {κ b:ℝ}
    (same:∀x,T.menu.terms x=R.menu.terms x) (B:ForcedBudget p T w κ b) :
    Nonempty (ForcedBudget p R w κ b) := by
  have tag i j:T.menu.marks i j=R.menu.marks i j:=congrArg (fun a:Bands Γ Q=>a.marks i j) (same z)
  have slot x i j U:T.menu.force x i j U=R.menu.force x i j U:=
    congrArg (fun a:Bands Γ Q=>a.entries i j U) (same x)
  refine ⟨{black:=B.black,black_nonnegative:=B.black_nonnegative,forced:=?_,total:=?_}⟩
  · intro x i j U
    rw [←slot]
    exact B.forced x i j U
  · intro v
    simpa only [←tag] using B.total v

def increase (p:BudgetPoint) (off:ℕ) (budget κ k b:ℝ) :=
  2*(Fintype.card Γ.Mode:ℝ)*(k+(Fintype.card V:ℝ)*(κ*b))*charge P p off budget/κ

theorem indexed_family (K:Guard.Keeper Q.p Q.activities) (H:P.Paid p a region w g width budget off cov) (bc:0≤budget) (hg:g≠0)
    (point:∀v,o v∈a v) (c:ℂ) (hc:‖c‖≤1) (T:Taste (TestSpace D) o Q Γ)
    {κ k b:ℝ} (validated:Q.activities.ForcedFamily Q.p) (live:∀x,(T.leaf x).Active)
    (before:∀x,Financed (T.menu.terms x))
    (divisor:0<κ) (hK:Q.activities.KBound p k) (B:ForcedBudget p (pullback (testInclusion D) T) w κ b)
    (small:2*(k+(Fintype.card V:ℝ)*(κ*b))*blockSites p.B≤(3*p.supportExponent)/2)
    (room:2*(Fintype.card V:ℝ)*(Fintype.card Γ.Mode:ℝ)*charge P p off budget≤1) :
    ∃A:Compulsory (TestSpace D) Γ G n, (Multilinear D T → Multilinear D (replace T A)) ∧
      Nonempty (ForcedBudget p (pullback (testInclusion D) (replace T A)) w κ (b+increase P p off budget κ k b)) ∧
      ∀x,((replace T A).leaf x).Active ∧ Financed ((replace T A).menu.terms x) ∧ ∀U,
        ((replace T A).leaf x).contents.cluster U=Poly.pass (c • dirty P Q.p x g U)*(T.leaf x).contents.cluster U ∧
        ((replace T A).leaf x).density U=Poly.pass (c • dirty P Q.p x g U)*(T.leaf x).density U := by
  let u:=k+(Fintype.card V:ℝ)*(κ*b)
  let fee:=charge P p off budget
  let piece:=2*u*fee/κ
  let F:=source (Q:=Q) P H hg c
  have u0:0≤u:=by
    have prior:=QLocalForcedTestForest.rows p (pullback (testInclusion D) T) B H.positive
      (fun i j=>(live (testInclusion D (zeroIndependentTests D))).articles.occurs i j) hK
    exact budget_nonneg (prior.choose_spec.2.1 0)
  have fee0:0≤fee:=by
    have ex:=p.exponent_pos
    dsimp [fee,charge,blockSites]
    positivity
  have piece0:0≤piece:=by dsimp [piece]; positivity
  let Good (A:TestSpace D→Bands Γ Q) (j:ℕ):=
    (∀x,(A x).origins=o ∧ (A x).Active) ∧ ∃Z:Taste (TestSpace D) o Q Γ,
      (∀x,A x=Z.menu.terms x) ∧ Nonempty (ForcedBudget p (pullback (testInclusion D) Z) w κ (b+(j:ℝ)*piece))
  have start:Good T.menu.terms 0:=⟨fun x=>⟨T.root,(live x).articles⟩,T,fun _=>rfl,by simpa using Nonempty.intro B⟩
  have step (A:TestSpace D→Bands Γ Q) (j:ℕ) (hj:j<Fintype.card Γ.Mode) (info:Good A j)
      (fin:∀x,Financed (A x)) (s:Γ.Mode) (hs:s≠Γ.quiet) :
      Good (fun x=>bands (A x) (addition (Y:=plot P) K (A x) s (F.field s x))) (j+1):=by
    obtain ⟨Z,same,⟨asset⟩⟩:=info.2
    have eq:A=Z.menu.terms:=funext same
    subst A
    let d x:=addition (Y:=plot P) K (Z.menu.terms x) s (F.field s x)
    let next:=replace Z (tape Z d)
    have all x:(bands (Z.menu.terms x) (d x)).Active:=by
      have law:=QLocalThermalJoinedLaw.charged (Q:=Q) P H o point s x c
      have ok:=QLocalMarkedJoinedEligibility.issued K (Z.menu.terms x) (info.1 x).2 validated (fin x).1
        s (F.field s x) ((info.1 x).1.symm ▸ law)
      exact QLocalCompulsoryJoinedTape.active _ (info.1 x).2 _ ok
    refine ⟨fun x=>⟨(info.1 x).1,all x⟩,next,fun _=>rfl,?_⟩
    have prior:=QLocalForcedTestForest.rows p (pullback (testInclusion D) Z) asset H.positive
      (fun i j=>(info.1 (testInclusion D (zeroIndependentTests D))).2.occurs i j) hK
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
    obtain ⟨ticket⟩:=coupon P K H s hs c hc Z.menu.terms
      (relax _ (show Towed w (ActualWilsonPacketSplit.scopes Q) (measured Z.menu.terms) p.B p.supportExponent _ from prior) amount) small
    obtain ⟨account⟩ := QLocalMarkedJoinedForcedBudget.serial (fun x=>d ((testInclusion D) x))
      (pullback (testInclusion D) Z) H.positive divisor asset ticket
    have values (x : IndependentTests D) :
        (replace (pullback (testInclusion D) Z) (QLocalCompulsoryJoinedTape.tape (pullback (testInclusion D) Z) (fun y=>d ((testInclusion D) y)))).menu.terms x =
          (pullback (testInclusion D) next).menu.terms x := rfl
    have carried := follows (zeroIndependentTests D) _ _ values account
    have money : b+(j:ℝ)*piece+(Fintype.card Γ.Mode:ℝ)*
        ((2/(3*p.supportExponent))*((2*u)*blockSites p.B)*
          ((2:ℝ)^P.rankCap*Real.exp (4*p.supportExponent*(off:ℝ))*budget))/κ = b+((j+1:ℕ):ℝ)*piece := by
      push_cast
      dsimp [piece,fee,charge]
      ring
    exact money ▸ carried
  have quiet x U:(c • dirty P Q.p x g U).part Γ.quiet=0:=by
    rw [Poly.part_smul,QLocalThermalPacketDivision.dirty,QLocalThermalPacketDivision.part,(WilsonPrescribedPacketTail.slice P _).quiet_read,mul_zero]
  let Both (A:TestSpace D→Bands Γ Q) (j:ℕ):=Good A j ∧ (Multilinear D T → QLocalMarkedJoinedLetters.Knows (o:=o) A)
  have initial:Both T.menu.terms 0:=⟨start,fun h=>⟨T,fun _=>rfl,h⟩⟩
  have advance (A:TestSpace D→Bands Γ Q) (j:ℕ) (hj:j<Fintype.card Γ.Mode) (ha:Both A j)
      (fin:∀x,Financed (A x)) (s:Γ.Mode) (hs:s≠Γ.quiet) :
      Both (fun x=>bands (A x) (addition (Y:=plot P) K (A x) s (F.field s x))) (j+1):=by
    exact ⟨step A j hj ha.1 fin s hs,fun h=>QLocalMarkedJoinedLetters.next K (ha.2 h) fin s (F.field s)
      (QLocalMarkedJoinedLetters.field P H Q.p c s)⟩
  obtain ⟨A,⟨ledger,letters⟩,full⟩:=QLocalMarkedJoinedFamily.issued K T F quiet Both initial before advance
  obtain ⟨Z,ident,⟨asset⟩⟩:=ledger.2
  have equal x:(pullback (testInclusion D) Z).menu.terms x=(pullback (testInclusion D) (replace T A)).menu.terms x:=
    (ident (testInclusion D x)).symm
  obtain ⟨bought⟩:=follows (zeroIndependentTests D) _ _ equal asset
  have count:((Finset.univ.erase Γ.quiet).card:ℝ)≤(Fintype.card Γ.Mode:ℝ):=by
    exact_mod_cast Finset.card_le_univ (Finset.univ.erase Γ.quiet)
  have extension : ((Finset.univ.erase Γ.quiet).card:ℝ)*piece ≤ increase P p off budget κ k b :=
    (mul_le_mul_of_nonneg_right count piece0).trans_eq (by dsimp [increase,piece,u,fee]; ring)
  have wallet : Nonempty (ForcedBudget p (pullback (testInclusion D) (replace T A)) w κ (b+increase P p off budget κ k b)) := by
    refine ⟨{bought with total:=?_}⟩
    intro v
    exact budget_loosen (bought.total v) (mul_le_mul_of_nonneg_left (add_le_add le_rfl extension) divisor.le)
  exact ⟨A,(fun h=>QLocalMarkedJoinedLetters.recovered T h A (letters h)),wallet,
    fun x=>⟨⟨(ledger.1 x).2,(live x).captions⟩,full x⟩⟩

theorem indexed_financed (K:Guard.Keeper Q.p Q.activities) (H:P.Paid p a region w g width budget off cov) (bc:0≤budget) (hg:g≠0)
    (point:∀v,o v∈a v) (c:ℂ) (hc:‖c‖≤1) (T:Taste (TestSpace D) o Q Γ)
    {e f κ k b:ℝ} (well:Q.activities.Valid Q.p e f) (live:∀x,(T.leaf x).Active)
    (before:∀x,Financed (T.menu.terms x))
    (divisor:0<κ) (hK:Q.activities.KBound p k) (B:ForcedBudget p (pullback (testInclusion D) T) w κ b)
    (small:2*(k+(Fintype.card V:ℝ)*(κ*b))*blockSites p.B≤(3*p.supportExponent)/2)
    (room:2*(Fintype.card V:ℝ)*(Fintype.card Γ.Mode:ℝ)*charge P p off budget≤1) :
    ∃A:Compulsory (TestSpace D) Γ G n, (Multilinear D T → Multilinear D (replace T A)) ∧
      Nonempty (ForcedBudget p (pullback (testInclusion D) (replace T A)) w κ (b+increase P p off budget κ k b)) ∧
      ∀x,((replace T A).leaf x).Active ∧ Financed ((replace T A).menu.terms x) ∧ ∀U,
        ((replace T A).leaf x).contents.cluster U=Poly.pass (c • dirty P Q.p x g U)*(T.leaf x).contents.cluster U ∧
        ((replace T A).leaf x).density U=Poly.pass (c • dirty P Q.p x g U)*(T.leaf x).density U :=
  indexed_family P K H bc hg point c hc T well.forced live before divisor hK B small room

theorem indexed_letters (K:Guard.Keeper Q.p Q.activities) (H:P.Paid p a region w g width budget off cov) (bc:0≤budget) (hg:g≠0)
    (point:∀v,o v∈a v) (c:ℂ) (hc:‖c‖≤1) (T:Taste (TestSpace D) o Q Γ)
    {e f κ k b:ℝ} (well:Q.activities.Valid Q.p e f) (live:∀x,(T.leaf x).Active)
    (fare:∀x,∃u v b t,(T.menu.terms x).Radial w u v b t)
    (divisor:0<κ) (hK:Q.activities.KBound p k) (B:ForcedBudget p (pullback (testInclusion D) T) w κ b)
    (small:2*(k+(Fintype.card V:ℝ)*(κ*b))*blockSites p.B≤(3*p.supportExponent)/2)
    (room:2*(Fintype.card V:ℝ)*(Fintype.card Γ.Mode:ℝ)*charge P p off budget≤1) :
    ∃A:Compulsory (TestSpace D) Γ G n, (Multilinear D T → Multilinear D (replace T A)) ∧
      Nonempty (ForcedBudget p (pullback (testInclusion D) (replace T A)) w κ (b+increase P p off budget κ k b)) ∧
      ∀x,((replace T A).leaf x).Active ∧ Financed ((replace T A).menu.terms x) ∧ ∀U,
        ((replace T A).leaf x).contents.cluster U=Poly.pass (c • dirty P Q.p x g U)*(T.leaf x).contents.cluster U ∧
        ((replace T A).leaf x).density U=Poly.pass (c • dirty P Q.p x g U)*(T.leaf x).density U := by
  apply indexed_financed P K H bc hg point c hc T well live ?_ divisor hK B small room
  intro x
  obtain ⟨u,v,b,t,m⟩:=fare x
  exact ⟨fun i U=>((T.menu.terms x).baseBound (live x).articles m well U).1 i,
    fun U=>((T.menu.terms x).population (live x).articles m well U).1⟩

theorem indexed (K:Guard.Keeper Q.p Q.activities) (H:P.Paid p a region w g width budget off cov) (bc:0≤budget) (hg:g≠0)
    (point:∀v,o v∈a v) (c:ℂ) (hc:‖c‖≤1) (T:Taste (TestSpace D) o Q Γ)
    {e f κ k b:ℝ} (well:Q.activities.Valid Q.p e f) (live:∀x,(T.leaf x).Active)
    (fare:∀x,∃u v b t,(T.menu.terms x).Radial w u v b t)
    (divisor:0<κ) (hK:Q.activities.KBound p k) (B:ForcedBudget p (pullback (testInclusion D) T) w κ b)
    (small:2*(k+(Fintype.card V:ℝ)*(κ*b))*blockSites p.B≤(3*p.supportExponent)/2)
    (room:2*(Fintype.card V:ℝ)*(Fintype.card Γ.Mode:ℝ)*charge P p off budget≤1) :
    ∃A:Compulsory (TestSpace D) Γ G n,
      Nonempty (ForcedBudget p (pullback (testInclusion D) (replace T A)) w κ (b+increase P p off budget κ k b)) ∧
      ∀x,((replace T A).leaf x).Active ∧ Financed ((replace T A).menu.terms x) ∧ ∀U,
        ((replace T A).leaf x).contents.cluster U=Poly.pass (c • dirty P Q.p x g U)*(T.leaf x).contents.cluster U ∧
        ((replace T A).leaf x).density U=Poly.pass (c • dirty P Q.p x g U)*(T.leaf x).density U := by
  obtain ⟨A,_,money,field⟩:=indexed_letters P K H bc hg point c hc T well live fare divisor hK B small room
  exact ⟨A,money,field⟩

end YM.Integration.QLocalThermalJoinedForcedRegister
