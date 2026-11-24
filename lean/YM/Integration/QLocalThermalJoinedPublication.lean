import YM.Integration.QLocalThermalJoinedRate
import YM.Integration.QLocalMarkedJoinedFamily

/-! Simultaneous physical cluster identity, true support and independent
per-site forcing price on the very same chosen finite tape. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalThermalJoinedPublication
open Function Finset Lattice RG Wilson Marker Overlay Extra.Histories Planned.GuardedAtom
open RG3.Script.Picnic LocalComparison Comparison.Density.RenderM MergeProof.Accent Push.AbsoluteSums
open ActualWilsonJoinedCofactor ActualWilsonDirtyPartners QLocalThermalPacketDivision QLocalThermalJoinedSource
open QLocalThermalJoinedRate QLocalCompulsoryJoinedTape QLocalMarkedJoinedLinear QLocalMarkedJoinedCatalogue
open WilsonLimitConstruction.FundedMarkedFieldSplit
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V] {Q:Rep G n}
    {D:V→ ComparisonDensity.Address.Orbit} {Γ:Census V} {o:V→Site n} {p:BudgetPoint}
    (P:MarkedPackets D G n Γ) {a:V→Support n} {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width budget:ℝ} {off cov:ℕ}

theorem zero {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V] {Q:Rep G n} {Γ:Census V} {p:BudgetPoint} {w:V→ℝ} {X:Type*} :
    Towed w (ActualWilsonPacketSplit.scopes Q) (fun _ (_:X)=>(0:Poly Γ)) p.B p.supportExponent 0 := by
  refine ⟨fun _=>0,summable_zero,?_,fun _=>⟨0,le_rfl,fun _ _=>by simp,by simp [Push.GridApprox.Nil.wordsPrice]⟩⟩
  intro site
  have all:SumBudget (fun _:ℕ=>(0:ℝ)) 0:=⟨fun _=>le_rfl,summable_zero,by simp⟩
  simpa only [zero_mul,ite_self] using all

theorem released (K:Guard.Keeper Q.p Q.activities) (H:P.Paid p a region w g width budget off cov) (budget0:0≤budget) (hg:g≠0)
    (point:∀v,o v∈a v) (c:ℂ) (hc:‖c‖≤1) (T:Taste (TestSpace D) o Q Γ)
    {d k u:ℝ} (well:Q.activities.Valid Q.p d k) (live:∀x,(T.leaf x).Active)
    (fare:∀x,∃u v b t,(T.menu.terms x).Radial w u v b t)
    (old:Towed w (ActualWilsonPacketSplit.scopes Q) (measured T.menu.terms) p.B p.supportExponent u)
    (small:2*u*blockSites p.B≤(3*p.supportExponent)/2)
    (room:2*(Fintype.card Γ.Mode:ℝ)*charge P p off budget≤1) :
    ∃A:Compulsory (TestSpace D) Γ G n,
      Towed w (ActualWilsonPacketSplit.scopes Q) (fun i z=>measured (replace T A).menu.terms i z-measured T.menu.terms i z)
        p.B p.supportExponent (2*(Fintype.card Γ.Mode:ℝ)*u*charge P p off budget) ∧ ∀x,
      ((replace T A).leaf x).Active ∧ Financed ((replace T A).menu.terms x) ∧ ∀U,
        ((replace T A).leaf x).contents.cluster U=Poly.pass (c • dirty P Q.p x g U)*(T.leaf x).contents.cluster U ∧
        ((replace T A).leaf x).density U=Poly.pass (c • dirty P Q.p x g U)*(T.leaf x).density U := by
  let fee:=charge P p off budget
  let piece:=2*u*fee
  let F:=source (Q:=Q) P H hg c
  have u0:0≤u:=budget_nonneg (old.choose_spec.2.1 0)
  have fee0:0≤fee:=by
    have ex:=p.exponent_pos
    dsimp [fee,charge,blockSites]
    positivity
  have piece0:0≤piece:=mul_nonneg (mul_nonneg (by norm_num) u0) fee0
  let Good (a:TestSpace D→Bands Γ Q) (j:ℕ):=
    (∀x,(a x).origins=o ∧ (a x).Active) ∧ Towed w (ActualWilsonPacketSplit.scopes Q)
      (fun i z=>measured a i z-measured T.menu.terms i z) p.B p.supportExponent ((j:ℝ)*piece)
  have base:Good T.menu.terms 0:=by
    refine ⟨fun x=>⟨T.root,(live x).articles⟩,?_⟩
    simpa only [sub_self,Nat.cast_zero,zero_mul] using (zero (Q:=Q) (Γ:=Γ) (p:=p) (w:=w))
  have before (x:TestSpace D):Financed (T.menu.terms x):=by
    obtain ⟨u,v,b,t,m⟩:=fare x
    exact ⟨fun i U=>((T.menu.terms x).baseBound (live x).articles m well U).1 i,
      fun U=>((T.menu.terms x).population (live x).articles m well U).1⟩
  have advance (a:TestSpace D→Bands Γ Q) (j:ℕ) (size:j<Fintype.card Γ.Mode)
      (last:Good a j) (funds:∀x,Financed (a x)) (s:Γ.Mode) (hs:s≠Γ.quiet) :
      Good (fun x=>bands (a x) (addition (Y:=plot P) K (a x) s (F.field s x))) (j+1):=by
    have whole:Towed w (ActualWilsonPacketSplit.scopes Q) (measured a) p.B p.supportExponent (u+(j:ℝ)*piece):=by
      have add:=plus (ActualWilsonPacketSplit.scopes Q) old last.2
      simpa only [add_sub_cancel] using add
    have bound:u+(j:ℝ)*piece≤2*u:=by
      have hj:(j:ℝ)≤(Fintype.card Γ.Mode:ℝ):=by exact_mod_cast size.le
      have k:=mul_le_mul_of_nonneg_left room u0
      have h:=mul_le_mul_of_nonneg_right hj piece0
      dsimp only [piece,fee] at h ⊢
      nlinarith only [h,k]
    have paid:=one P K H s hs c hc a (relax _ whole bound) small
    have gain:Towed w (ActualWilsonPacketSplit.scopes Q) (fun i (z:IndependentTests D × Config G n)=>addition (Y:=plot P) K
        (a (testInclusion D z.1)) s (F.field s (testInclusion D z.1)) i z.2)
        p.B p.supportExponent piece:=paid
    constructor
    · intro x
      let law:=QLocalThermalJoinedLaw.charged (Q:=Q) P H o point s x c
      have ok:=QLocalMarkedJoinedEligibility.issued K (a x) (last.1 x).2 well.forced (funds x).1
          s (F.field s x) ((last.1 x).1.symm ▸ law)
      exact ⟨(last.1 x).1,QLocalCompulsoryJoinedTape.active _ (last.1 x).2 _ ok⟩
    have move:=plus (ActualWilsonPacketSplit.scopes Q) last.2 gain
    convert move using 1
    · funext i z
      unfold measured
      rw [QLocalCompulsoryJoinedTape.each _ _ _ _ (silence K _ s hs _ i z.2) ((funds _).1 i z.2)]
      abel
    · push_cast; ring
  have quiet (x:TestSpace D) (U:Config G n):(c • dirty P Q.p x g U).part Γ.quiet=0:=by
    rw [Poly.part_smul,QLocalThermalPacketDivision.dirty,QLocalThermalPacketDivision.part,(WilsonPrescribedPacketTail.slice P _).quiet_read,mul_zero]
  obtain ⟨A,earned,all⟩:=QLocalMarkedJoinedFamily.issued K T F quiet Good base before advance
  refine ⟨A,relax _ earned.2 ?_,fun x=>⟨⟨(earned.1 x).2,(live x).captions⟩,all x⟩⟩
  have card:((Finset.univ.erase Γ.quiet).card:ℝ)≤(Fintype.card Γ.Mode:ℝ):=by
    exact_mod_cast (Finset.card_le_univ (Finset.univ.erase Γ.quiet))
  exact (mul_le_mul_of_nonneg_right card piece0).trans_eq (by dsimp [piece,fee]; ring)

end YM.Integration.QLocalThermalJoinedPublication
