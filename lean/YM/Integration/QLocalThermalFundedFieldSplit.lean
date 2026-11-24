import YM.Integration.QLocalThermalJoinedForcedRegister
import YM.Integration.QLocalLaurentOrderTail

/-! A single full field split on the actual marked path bank with the
honest thermal budget stored at each of the returned forced addresses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalThermalFundedFieldSplit
open Function Finset Lattice RG Wilson Marker Overlay Extra.Histories Planned.GuardedAtom
open RG3.Script.Picnic LocalComparison LocalComparison.Global Comparison.Density.RenderM
open QLocalThermalPacketDivision ActualWilsonDirtyPartners QLocalThermalJoinedRate QLocalThermalJoinedForcedRegister
open WilsonLimitConstruction.FundedMarkedFieldSplit
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V] {Q:Rep G n}
    {D:V→ ComparisonDensity.Address.Orbit} {Γ:Census V} {o:V→Site n} {p:BudgetPoint}
    (P:MarkedPackets D G n Γ) {a:V→Support n} {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width budget:ℝ} {off cov:ℕ}

def Series (T:Taste (TestSpace D) o Q Γ) : Prop := ∀x,QLocalMarkedJoinedCatalogue.Financed (T.menu.terms x) ∧
  ∀U,Summable (fun i=>(T.leaf x).contents.ray i U)

theorem from_radial (T:Taste (TestSpace D) o Q Γ) {e k:ℝ} (good:Q.activities.Valid Q.p e k)
    (live:∀x,(T.leaf x).Active) (fare:∀x,∃u v b t,(T.menu.terms x).Radial w u v b t) : Series T := by
  intro x
  obtain ⟨u,v,b,t,pay⟩:=fare x
  exact ⟨⟨fun i U=>((T.menu.terms x).baseBound (live x).articles pay good U).1 i,
    fun U=>((T.menu.terms x).population (live x).articles pay good U).1⟩,
    fun U=>((T.menu.terms x).bulkBound (live x).articles pay U).1⟩

theorem issued_series (K:Guard.Keeper Q.p Q.activities) (H:P.Paid p a region w g width budget off cov)
    (bc:0≤budget) (hg:g≠0) (point:∀v,o v∈a v) (F E:Taste (TestSpace D) o Q Γ)
    {e k k' κ b b':ℝ} (good:Q.activities.Valid Q.p e k) (fl:∀x,(F.leaf x).Active) (el:∀x,(E.leaf x).Active)
    (ff:Series F) (ef:Series E)
    (positive:0<κ) (hK:Q.activities.KBound p k')
    (B:ForcedBudget p (pullback (testInclusion D) F) w κ b) (B':ForcedBudget p (pullback (testInclusion D) E) w κ b')
    (small:2*(k'+(Fintype.card V:ℝ)*(κ*b))*blockSites p.B≤(3*p.supportExponent)/2)
    (small':2*(k'+(Fintype.card V:ℝ)*(κ*b'))*blockSites p.B≤(3*p.supportExponent)/2)
    (room:2*(Fintype.card V:ℝ)*(Fintype.card Γ.Mode:ℝ)*charge P p off budget≤1) :
    ∃ticket:Invoice F E (fun x U=>P.read x g U),
      ticket.soft=QLocalThermalPacketRebooking.regular P (F.menu.rays 0) g ∧
      (Multilinear D F → Multilinear D (replace F ticket.formalForced)) ∧
      (Multilinear D E → Multilinear D (replace E ticket.residualForced)) ∧
      Nonempty (ForcedBudget p (pullback (testInclusion D) (replace F ticket.formalForced)) w κ
        (b+increase P p off budget κ k' b)) ∧
      Nonempty (ForcedBudget p (pullback (testInclusion D) (replace E ticket.residualForced)) w κ
        (b'+increase P p off budget κ k' b')) := by
  obtain ⟨A,ma,ba,fa⟩:=indexed_financed P K H bc hg point (-1) (by norm_num) F good fl (fun x=>(ff x).1) positive hK B small room
  obtain ⟨C,mb,bb,eb⟩:=indexed_financed P K H bc hg point 1 (by norm_num) E good el (fun x=>(ef x).1) positive hK B' small' room
  refine ⟨{
    soft := QLocalThermalPacketRebooking.regular P (F.menu.rays 0) g
    hard := fun x U=>dirty P Q.p x g U
    quiet := fun _ _=>(WilsonPrescribedPacketTail.slice P _).quiet_read _ _ _
    formalForced := A
    residualForced := C
    formal_active := fun x=>(fa x).1
    residual_active := fun x=>(eb x).1
    formal_sum := ?_
    residual_sum := ?_
    masked := ?_
    formal_cluster := ?_
    residual_cluster := ?_
  },rfl,ma,mb,ba,bb⟩
  · intro x U
    exact (ff x).2 U
  · intro x U
    exact (ef x).2 U
  · intro x U
    exact (QLocalThermalPacketRebooking.soft P (F.menu.rays 0) H hg x U).trans_eq
      (congrArg nhds (eq_sub_iff_add_eq.mpr (partition P Q.p H hg x U).2))
  · intro x U
    simpa only [neg_one_smul] using (((fa x).2.2 U).1)
  · intro x U
    simpa only [one_smul] using (((eb x).2.2 U).1)

theorem issued_letters (K:Guard.Keeper Q.p Q.activities) (H:P.Paid p a region w g width budget off cov)
    (bc:0≤budget) (hg:g≠0) (point:∀v,o v∈a v) (F E:Taste (TestSpace D) o Q Γ)
    {e k k' κ b b':ℝ} (good:Q.activities.Valid Q.p e k) (fl:∀x,(F.leaf x).Active) (el:∀x,(E.leaf x).Active)
    (ff:∀x,∃u v b t,(F.menu.terms x).Radial w u v b t) (ef:∀x,∃u v b t,(E.menu.terms x).Radial w u v b t)
    (positive:0<κ) (hK:Q.activities.KBound p k')
    (B:ForcedBudget p (pullback (testInclusion D) F) w κ b) (B':ForcedBudget p (pullback (testInclusion D) E) w κ b')
    (small:2*(k'+(Fintype.card V:ℝ)*(κ*b))*blockSites p.B≤(3*p.supportExponent)/2)
    (small':2*(k'+(Fintype.card V:ℝ)*(κ*b'))*blockSites p.B≤(3*p.supportExponent)/2)
    (room:2*(Fintype.card V:ℝ)*(Fintype.card Γ.Mode:ℝ)*charge P p off budget≤1) :
    ∃ticket:Invoice F E (fun x U=>P.read x g U),
      ticket.soft=QLocalThermalPacketRebooking.regular P (F.menu.rays 0) g ∧
      (Multilinear D F → Multilinear D (replace F ticket.formalForced)) ∧
      (Multilinear D E → Multilinear D (replace E ticket.residualForced)) ∧
      Nonempty (ForcedBudget p (pullback (testInclusion D) (replace F ticket.formalForced)) w κ
        (b+increase P p off budget κ k' b)) ∧
      Nonempty (ForcedBudget p (pullback (testInclusion D) (replace E ticket.residualForced)) w κ
        (b'+increase P p off budget κ k' b')) := by
  exact issued_series P K H bc hg point F E good fl el (from_radial F good fl ff)
    (from_radial E good el ef) positive hK B B' small small' room

theorem issued_rows (K:Guard.Keeper Q.p Q.activities) (H:P.Paid p a region w g width budget off cov)
    (bc:0≤budget) (hg:g≠0) (point:∀v,o v∈a v) (F E:Taste (TestSpace D) o Q Γ)
    {e k k' κ b b':ℝ} (good:Q.activities.Valid Q.p e k) (fl:∀x,(F.leaf x).Active) (el:∀x,(E.leaf x).Active)
    (ff:∀x,∃u v b t,(F.menu.terms x).Radial w u v b t) (ef:∀x,∃u v b t,(E.menu.terms x).Radial w u v b t)
    (positive:0<κ) (hK:Q.activities.KBound p k')
    (B:ForcedBudget p (pullback (testInclusion D) F) w κ b) (B':ForcedBudget p (pullback (testInclusion D) E) w κ b')
    (small:2*(k'+(Fintype.card V:ℝ)*(κ*b))*blockSites p.B≤(3*p.supportExponent)/2)
    (small':2*(k'+(Fintype.card V:ℝ)*(κ*b'))*blockSites p.B≤(3*p.supportExponent)/2)
    (room:2*(Fintype.card V:ℝ)*(Fintype.card Γ.Mode:ℝ)*charge P p off budget≤1) :
    ∃ticket:Invoice F E (fun x U=>P.read x g U),
      ticket.soft=QLocalThermalPacketRebooking.regular P (F.menu.rays 0) g ∧
      Nonempty (ForcedBudget p (pullback (testInclusion D) (replace F ticket.formalForced)) w κ
        (b+increase P p off budget κ k' b)) ∧
      Nonempty (ForcedBudget p (pullback (testInclusion D) (replace E ticket.residualForced)) w κ
        (b'+increase P p off budget κ k' b')) := by
  obtain ⟨S,rows,_,_,a,b⟩:=issued_letters P K H bc hg point F E good fl el ff ef positive hK B B' small small' room
  exact ⟨S,rows,a,b⟩

theorem issued (K:Guard.Keeper Q.p Q.activities) (H:P.Paid p a region w g width budget off cov)
    (bc:0≤budget) (hg:g≠0) (point:∀v,o v∈a v) (F E:Taste (TestSpace D) o Q Γ)
    {e k k' κ b b':ℝ} (good:Q.activities.Valid Q.p e k) (fl:∀x,(F.leaf x).Active) (el:∀x,(E.leaf x).Active)
    (ff:∀x,∃u v b t,(F.menu.terms x).Radial w u v b t) (ef:∀x,∃u v b t,(E.menu.terms x).Radial w u v b t)
    (positive:0<κ) (hK:Q.activities.KBound p k')
    (B:ForcedBudget p (pullback (testInclusion D) F) w κ b) (B':ForcedBudget p (pullback (testInclusion D) E) w κ b')
    (small:2*(k'+(Fintype.card V:ℝ)*(κ*b))*blockSites p.B≤(3*p.supportExponent)/2)
    (small':2*(k'+(Fintype.card V:ℝ)*(κ*b'))*blockSites p.B≤(3*p.supportExponent)/2)
    (room:2*(Fintype.card V:ℝ)*(Fintype.card Γ.Mode:ℝ)*charge P p off budget≤1) :
    ∃ticket:Invoice F E (fun x U=>P.read x g U),
      Nonempty (ForcedBudget p (pullback (testInclusion D) (replace F ticket.formalForced)) w κ
        (b+increase P p off budget κ k' b)) ∧
      Nonempty (ForcedBudget p (pullback (testInclusion D) (replace E ticket.residualForced)) w κ
        (b'+increase P p off budget κ k' b')) := by
  obtain ⟨S,_,a,b⟩:=issued_rows P K H bc hg point F E good fl el ff ef positive hK B B' small small' room
  exact ⟨S,a,b⟩

theorem high (K:Guard.Keeper Q.p Q.activities) (H:P.Paid p a region w 1 width budget off cov)
    (bc:0≤budget) (hg:0<g) (hs:g≤1) (ord:ℕ) (point:∀v,o v∈a v) (F E:Taste (TestSpace D) o Q Γ)
    {e k k' κ b b':ℝ} (good:Q.activities.Valid Q.p e k) (fl:∀x,(F.leaf x).Active) (el:∀x,(E.leaf x).Active)
    (ff:∀x,∃u v b t,(F.menu.terms x).Radial w u v b t) (ef:∀x,∃u v b t,(E.menu.terms x).Radial w u v b t)
    (positive:0<κ) (hK:Q.activities.KBound p k')
    (B:ForcedBudget p (pullback (testInclusion D) F) w κ b) (B':ForcedBudget p (pullback (testInclusion D) E) w κ b')
    (small:2*(k'+(Fintype.card V:ℝ)*(κ*b))*blockSites p.B≤(3*p.supportExponent)/2)
    (small':2*(k'+(Fintype.card V:ℝ)*(κ*b'))*blockSites p.B≤(3*p.supportExponent)/2)
    (room:2*(Fintype.card V:ℝ)*(Fintype.card Γ.Mode:ℝ)*
      charge (QLocalLaurentOrderTail.upper P ord) p off (g^(ord+1)*budget)≤1) :
    let high:=QLocalLaurentOrderTail.upper P ord
    ∃ticket:Invoice F E (fun x U=>high.read x g U),
      Nonempty (ForcedBudget p (pullback (testInclusion D) (replace F ticket.formalForced)) w κ
        (b+increase high p off (g^(ord+1)*budget) κ k' b)) ∧
      Nonempty (ForcedBudget p (pullback (testInclusion D) (replace E ticket.residualForced)) w κ
        (b'+increase high p off (g^(ord+1)*budget) κ k' b')) := by
  exact issued _ K (QLocalLaurentOrderTail.paid P ord H hg hs) (mul_nonneg (pow_nonneg hg.le _) bc)
    hg.ne' point F E good fl el ff ef positive hK B B' small small' room

end YM.Integration.QLocalThermalFundedFieldSplit
