import YM.Integration.QLocalThermalJoinedLaw
import YM.Integration.QLocalMarkedJoinedLetters
import YM.Integration.LocalComparisonFunctionalRetains

/-! Keep the entire prescribed support of each independent test in every
physical joined hard slot, including its old partners and the new source.
The old tape and original scalar tail are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedSpringJoinedAddresses
open Function Set Finset MeasureTheory Lattice RG Wilson Marker Overlay
open Comparison.Density.Markers Extra.Histories Planned.GuardedAtom LocalComparison
open ActualWilsonPacketSplit ActualWilsonTaylorSlot QLocalMarkedJoinedLinear QLocalCompulsoryJoinedTape
open QLocalMarkedJoinedCatalogue QLocalThermalPacketDivision
open WilsonLimitConstruction.FundedMarkedFieldSplit RG3.Script.Picnic Comparison.Density.RenderM LocalComparison.MarkedPackets
open QLocalThermalJoinedSource
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {W : Rep G n} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
  {X : Type} {o : V→Site n} {Y : ℕ→Support n} (a : V→Support n)

def Held (B : Bands Γ W) : Prop := ∀i j U, B.entries i j U≠0 →
  ∀v∈(B.marks i j).val, a v⊆(W.activities.forced i).support

theorem prior {G : Gauge} {n : Side} {W : Rep G n} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {X : Type} {o : V→Site n} (a : V→Support n) (T : Taste X o W Γ) (h : FunctionalRetains T a) (x : X) : Held a (T.menu.terms x) :=
  fun i j U nz v hv=>h.forced i j v ⟨x,U,nz⟩ hv

theorem each {G : Gauge} {n : Side} {W : Rep G n} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} (a : V→Support n) (B : Bands Γ W) (h : Held a B) (i : ℕ) (U : Config G n) :
    Carries a (W.activities.forced i).support (B.each i U) := by
  intro s v hv out
  have hn:s≠Γ.quiet:=fun eq=>by simp [eq,Census.quiet] at hv
  have zero (j:ℕ):(B.tagged i j U).part s=0:=by
    rw [Bands.tagged,Poly.part_send]
    split
    next eq => by_contra nz; exact out (h i j U nz v (eq ▸ hv))
    rfl
  by_cases sum:Summable (fun j=>B.tagged i j U)
  · rw [Bands.each,Poly.part_plus,Poly.share sum,Poly.part_send,if_neg hn]
    simp only [zero,tsum_zero,zero_add]
  · simp [Bands.each,tsum_eq_zero_of_not_summable sum,Poly.part_send,hn]

theorem joined (K : Guard.Keeper W.p W.activities) (B : Bands Γ W) (h : Held a B) (s : Γ.Mode)
    (f : ℕ→ Config G n→ℂ) (support : ∀r U,f r U≠0 → ∀v∈s.val,a v⊆Y r) (i : ℕ) (U : Config G n) :
    Carries a (scopes W i) (addition (Y:=Y) K B s f i U) := by
  by_cases found:i∈Set.range (address (Y:=Y) K)
  · obtain ⟨z,rfl⟩:=found
    change Carries a (scopes W (address K z)) (QLocalMarkedJoinedCofactor.placed K
      (fun j=>B.each j U) (fun r=>Poly.send s (f r U)) U (address K z))
    rw [QLocalMarkedJoinedCofactor.on_slot,(geometry K z).1]
    by_cases admitted:gate z U
    · rw [QLocalMarkedJoinedCofactor.deposit,if_pos admitted]
      apply Carries.mul
      · intro t v hv out
        by_cases eq:t=s
        · subst t
          by_cases silent:f z.1.1 U=0
          · simp [silent]
          exact False.elim (out (fun y hy=>Finset.mem_union_left _ (support z.1.1 U silent v hv hy)))
        · simp [eq]
      · apply Carries.prod
        intro j hj t v hv out
        have reach:scopes W j⊆ActualWilsonPacketSplit.joined W (Y z.1.1) z.1.2:=
          fun _ hx=>Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨j,hj,hx⟩)
        exact each a B h j U t v hv (fun old=>out (old.trans reach))
    · simpa [QLocalMarkedJoinedCofactor.deposit,admitted] using
        (carry_zero (O:=a) (X:=ActualWilsonPacketSplit.joined W (Y z.1.1) z.1.2) (R:=Γ))
  · change Carries a (scopes W i) (QLocalMarkedJoinedCofactor.placed K
      (fun j=>B.each j U) (fun r=>Poly.send s (f r U)) U i)
    rw [QLocalMarkedJoinedCofactor.escaped K _ _ i U found]
    exact carry_zero

theorem next (K : Guard.Keeper W.p W.activities) (B : Bands Γ W) (h : Held a B) (s : Γ.Mode)
    (f : ℕ→ Config G n→ℂ) (support : ∀r U,f r U≠0 → ∀v∈s.val,a v⊆Y r) :
    Held a (bands B (addition (Y:=Y) K B s f)) := by
  intro i j U nz v hv
  obtain ⟨j,rfl⟩ := (QLocalCompulsoryInventoryBank.roster Γ).surjective j
  cases j with
  | inl j => exact h i j U (by simpa [bands,entry] using nz) v (by simpa [bands,QLocalCompulsoryInventoryBank.mode] using hv)
  | inr t =>
    by_cases quiet:t=Γ.quiet
    · exact False.elim (nz (by simp [bands,entry,quiet]))
    · by_contra escapes
      have inside:v∈t.val:=by simpa [bands,QLocalCompulsoryInventoryBank.mode,quiet] using hv
      apply nz
      simpa [bands,entry,quiet] using joined a K B h s f support i U t v inside escapes

theorem restored {G : Gauge} {n : Side} {W : Rep G n} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {X : Type} {o : V→Site n} (a : V→Support n) (T : Taste X o W Γ) (h : FunctionalRetains T a) (A : Compulsory X Γ G n)
    (full : ∀x,Held a ((replace T A).menu.terms x)) : FunctionalRetains (replace T A) a where
  origins := h.origins
  regular := h.regular
  captions := h.captions
  forced i j v nz hv := by
    obtain ⟨x,U,value⟩:=nz
    exact full x i j U value v hv

variable {D : V→ ComparisonDensity.Address.Orbit} (P : MarkedPackets D G n Γ)
    {p : BudgetPoint} {s₀ : Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w : V→ℝ} {g width budget : ℝ} {off cov : ℕ}

theorem token {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} (a : V→Support n) {D : V→ ComparisonDensity.Address.Orbit} (P : MarkedPackets D G n Γ)
    {p : BudgetPoint} {s₀ : Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w : V→ℝ} {g width budget : ℝ} {off cov : ℕ} (paid : P.Paid p a s₀ w g width budget off cov) (c : ℂ) (q : BudgetPoint) (s : Γ.Mode)
    (x : TestSpace D) (i : ℕ) (U : Config G n) (value : row P q g c s x i U≠0) :
    ∀v∈s.val,a v⊆plot P i := by
  have hs:s=P.mode i:=by by_contra bad; exact value (by simp [row,bad])
  intro v hv
  cases e:P.packet i with
  | none=>exact False.elim (value (by simp [row,MarkedPackets.term,e]))
  | some T=>simpa [plot,e] using paid.addresses i T e v (hs ▸ hv)

/-- Register every nonempty independent mode together on the prescribed addresses.
The same genuine returned tape has its complete ambient series and all independent
linear letters. The quantitative forced fee remains an independent component. -/
theorem registered (K : Guard.Keeper W.p W.activities) (paid : P.Paid p a s₀ w g width budget off cov)
    (hg : g≠0) (c : ℂ) (T : Taste (TestSpace D) o W Γ) (h : FunctionalRetains T a)
    (family : W.activities.ForcedFamily W.p) (live : ∀x,(T.leaf x).Active)
    (before : ∀x,Financed (T.menu.terms x)) :
    ∃A : Compulsory (TestSpace D) Γ G n, FunctionalRetains (replace T A) a ∧
      (Multilinear D T → Multilinear D (replace T A)) ∧ ∀x,
      ((replace T A).leaf x).Active ∧ Financed ((replace T A).menu.terms x) ∧ ∀U,
      ((replace T A).leaf x).contents.cluster U=Poly.pass (c • dirty P W.p x g U)*(T.leaf x).contents.cluster U ∧
      ((replace T A).leaf x).density U=Poly.pass (c • dirty P W.p x g U)*(T.leaf x).density U := by
  let F:=QLocalThermalJoinedSource.source (Q:=W) P paid hg c
  let CarriesAll (A : TestSpace D→Bands Γ W) (_ : ℕ) :=
    (∀x,(A x).origins=o ∧ (A x).Active ∧ Held a (A x)) ∧
    (Multilinear D T → QLocalMarkedJoinedLetters.Knows (o:=o) A)
  have initial : CarriesAll T.menu.terms 0 :=
    ⟨fun x=>⟨T.root,(live x).articles,prior a T h x⟩,fun l=>⟨T,fun _=>rfl,l⟩⟩
  have advance (A : TestSpace D→Bands Γ W) (j : ℕ) (_ : j<Fintype.card Γ.Mode) (pa : CarriesAll A j)
      (fund : ∀x,Financed (A x)) (s : Γ.Mode) (_ : s≠Γ.quiet) :
      CarriesAll (fun x=>bands (A x) (addition (Y:=plot P) K (A x) s (F.field s x))) (j+1) := by
    refine ⟨?_,fun l=>QLocalMarkedJoinedLetters.next K (pa.2 l) fund s (F.field s) (QLocalMarkedJoinedLetters.field P paid W.p c s)⟩
    intro x
    have law:=QLocalThermalJoinedLaw.charged (Q:=W) P paid o h.origins s x c
    have allowed:=QLocalMarkedJoinedEligibility.issued K (A x) (pa.1 x).2.1 family (fund x).1 s (F.field s x)
      ((pa.1 x).1.symm ▸ law)
    exact ⟨(pa.1 x).1,QLocalCompulsoryJoinedTape.active _ (pa.1 x).2.1 _ allowed,
      next a K (A x) (pa.1 x).2.2 s (F.field s x) (token a P paid c W.p s x)⟩
  have quiet x U:(c • dirty P W.p x g U).part Γ.quiet=0:=by
    rw [Poly.part_smul]
    change c * ((WilsonPrescribedPacketTail.slice P _).read x g U).part Γ.quiet=0
    rw [(WilsonPrescribedPacketTail.slice P _).quiet_read,mul_zero]
  obtain ⟨A,account,complete⟩:=QLocalMarkedJoinedFamily.issued K T F quiet CarriesAll initial before advance
  exact ⟨A,restored a T h A (fun x=>(account.1 x).2.2),
    fun l=>QLocalMarkedJoinedLetters.recovered T l A (account.2 l),
    fun x=>⟨⟨(account.1 x).2.1,(live x).captions⟩,complete x⟩⟩

end YM.Integration.WilsonLimitConstruction.FundedSpringJoinedAddresses
end
