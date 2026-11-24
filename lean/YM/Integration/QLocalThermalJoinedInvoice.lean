import YM.Integration.QLocalThermalJoinedLaw
import YM.Integration.QLocalThermalPacketRebooking

/-! A complete original signed emitted tape, including dirty terms whose
footprints span several original compulsory rows. All old signs and
higher mixed source modes are retained before any fields or tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalThermalJoinedInvoice
open Function Finset Lattice RG Wilson Marker Overlay Extra.Histories Planned.GuardedAtom
open RG3.Script.Picnic LocalComparison Comparison.Density.RenderM LocalComparison.MarkedPackets
open QLocalThermalPacketDivision QLocalMarkedJoinedCatalogue QLocalThermalJoinedSource
open WilsonLimitConstruction.FundedMarkedFieldSplit
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {Q:Rep G n} {V:Type} [DecidableEq V] [Fintype V]
    {D:V→ ComparisonDensity.Address.Orbit} {Γ:Census V} {o:V→Site n} (P:MarkedPackets D G n Γ)
    {p:BudgetPoint} {a:V→Support n} {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width budget:ℝ} {off cov:ℕ}

theorem released (K:Guard.Keeper Q.p Q.activities) (H:P.Paid p a region w g width budget off cov)
    (hg:g≠0) (point:∀v,o v∈a v) (c:ℂ) (T:Taste (TestSpace D) o Q Γ) {e k:ℝ}
    (well:Q.activities.Valid Q.p e k) (live:∀x,(T.leaf x).Active)
    (fare:∀x,∃u v b t,(T.menu.terms x).Radial w u v b t) :
    ∃A:Compulsory (TestSpace D) Γ G n,∀x,((replace T A).leaf x).Active ∧
      ∀U,((replace T A).leaf x).contents.cluster U=Poly.pass (c • dirty P Q.p x g U)*(T.leaf x).contents.cluster U ∧
        ((replace T A).leaf x).density U=Poly.pass (c • dirty P Q.p x g U)*(T.leaf x).density U := by
  let F:=source (Q:=Q) P H hg c
  let life (a:Bands Γ Q):=a.Active ∧ a.origins=o ∧ Financed a
  have before (x:TestSpace D):Financed (T.menu.terms x):=by
    obtain ⟨u,v,b,t,asset⟩:=fare x
    exact ⟨fun i U=>((T.menu.terms x).baseBound (live x).articles asset well U).1 i,
      fun U=>((T.menu.terms x).population (live x).articles asset well U).1⟩
  have after (a:Bands Γ Q) (s:Γ.Mode) (hs:s≠Γ.quiet) (x:TestSpace D) (old:life a) :
      life (QLocalCompulsoryJoinedTape.bands a (QLocalMarkedJoinedLinear.addition (Y:=plot P) K a s (F.field s x))) := by
    let receipt:=QLocalThermalJoinedLaw.charged (Q:=Q) P H o point s x c
    have eligible:=QLocalMarkedJoinedEligibility.issued K a old.1 well.forced old.2.2.1 s (F.field s x)
        (old.2.1.symm ▸ receipt)
    exact ⟨QLocalCompulsoryJoinedTape.active a old.1 _ eligible,old.2.1,
      fun i U=>QLocalCompulsoryJoinedTape.tagged _ _ i U (old.2.2.1 i U),
      fun U=>(QLocalMarkedJoinedRelease.issued K a s hs (F.field s x) U (fun r=>F.dirty s x r U)
        (F.purchase s x U).summable (fun i=>old.2.2.1 i U) (old.2.2.2 U)).1⟩
  have zero (x:TestSpace D) (U:Config G n):(c • dirty P Q.p x g U).part Γ.quiet=0:=by
    rw [Poly.part_smul]
    unfold dirty QLocalThermalPacketDivision.part
    rw [(WilsonPrescribedPacketTail.slice P _).quiet_read,mul_zero]
  obtain ⟨A,sold⟩:=QLocalMarkedJoinedCatalogue.issued K T F zero life
    (fun x=>⟨⟨(live x).articles,T.root,before x⟩,before x⟩) after
  exact ⟨A,fun x=>⟨⟨(sold x).1.1,(live x).captions⟩,(sold x).2.2⟩⟩

theorem invoice_rows (K:Guard.Keeper Q.p Q.activities) (H:P.Paid p a region w g width budget off cov)
    (hg:g≠0) (point:∀v,o v∈a v) (F E:Taste (TestSpace D) o Q Γ) {d k:ℝ} (well:Q.activities.Valid Q.p d k)
    (fl:∀x,(F.leaf x).Active) (el:∀x,(E.leaf x).Active)
    (ff:∀x,∃u v b t,(F.menu.terms x).Radial w u v b t)
    (ef:∀x,∃u v b t,(E.menu.terms x).Radial w u v b t) :
    ∃S:Invoice F E (fun x U=>P.read x g U), S.soft=QLocalThermalPacketRebooking.regular P (F.menu.rays 0) g := by
  obtain ⟨A,formal⟩:=released P K H hg point (-1) F well fl ff
  obtain ⟨B,residual⟩:=released P K H hg point 1 E well el ef
  refine ⟨{
    soft := QLocalThermalPacketRebooking.regular P (F.menu.rays 0) g
    hard := fun x U => dirty P Q.p x g U
    quiet := fun _ _ => (WilsonPrescribedPacketTail.slice P _).quiet_read _ _ _
    formalForced := A
    residualForced := B
    formal_active := fun x => (formal x).1
    residual_active := fun x => (residual x).1
    formal_sum := ?_
    residual_sum := ?_
    masked := ?_
    formal_cluster := ?_
    residual_cluster := ?_ },rfl⟩
  · intro x U
    obtain ⟨u,v,b,t,asset⟩:=ff x
    exact ((F.menu.terms x).bulkBound (fl x).articles asset U).1
  · intro x U
    obtain ⟨u,v,b,t,asset⟩:=ef x
    exact ((E.menu.terms x).bulkBound (el x).articles asset U).1
  · intro x U
    have hclear : clear P Q.p x g U = P.read x g U - dirty P Q.p x g U :=
      eq_sub_iff_add_eq.mpr (partition P Q.p H hg x U).2
    rw [←hclear]
    exact QLocalThermalPacketRebooking.soft P (F.menu.rays 0) H hg x U
  · intro x U
    simpa only [neg_one_smul] using ((formal x).2 U).1
  · intro x U
    simpa only [one_smul] using ((residual x).2 U).1

theorem invoice (K:Guard.Keeper Q.p Q.activities) (H:P.Paid p a region w g width budget off cov)
    (hg:g≠0) (point:∀v,o v∈a v) (F E:Taste (TestSpace D) o Q Γ) {d k:ℝ} (well:Q.activities.Valid Q.p d k)
    (fl:∀x,(F.leaf x).Active) (el:∀x,(E.leaf x).Active)
    (ff:∀x,∃u v b t,(F.menu.terms x).Radial w u v b t)
    (ef:∀x,∃u v b t,(E.menu.terms x).Radial w u v b t) :
    Nonempty (Invoice F E (fun x U=>P.read x g U)) := by
  obtain ⟨S,_⟩:=invoice_rows P K H hg point F E well fl el ff ef
  exact ⟨S⟩

end YM.Integration.QLocalThermalJoinedInvoice
