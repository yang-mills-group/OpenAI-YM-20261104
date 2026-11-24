import YM.Integration.QLocalMarkedJoinedCatalogue

/-! The original joined footprint includes the entire inserted token and
every original compulsory partner which touched it. This pays the native
support and visibility clauses for the existing marked tape. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalMarkedJoinedEligibility
open Function Set Finset MeasureTheory Lattice RG Wilson Marker Overlay
open Comparison.Density.Markers Extra.Histories Planned.GuardedAtom
open ActualWilsonPacketSplit ActualWilsonTaylorSlot QLocalMarkedJoinedLinear QLocalCompulsoryJoinedTape
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {W:Rep G n} {Y:ℕ→Support n} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V}

structure Law (o:V→Site n) (s:Γ.Mode) (f:ℕ→ Config G n→ℂ) : Prop where
  roots r U : f r U≠0→∀v∈s.val,o v∈Y r
  reads r : UsesFinal W.p.threshold (Y r) (f r)
  gauge r : GaugeInvariant (f r)
  measurable r : Measurable (f r)

theorem issued (K:Guard.Keeper W.p W.activities) (a:Bands Γ W) (A:a.Active)
    (well:W.activities.ForcedFamily W.p) (entries:∀i U,Summable (fun j=>a.tagged i j U))
    (s:Γ.Mode) (f:ℕ→ Config G n→ℂ) (paid:Law (W:=W) (Y:=Y) a.origins s f) :
    Eligible a (addition (Y:=Y) K a s f) := by
  let d:=addition (Y:=Y) K a s f
  let before:=QLocalCompulsoryInventoryLocal.original a A well entries
  let D (z:Key W Y) (U:Config G n):=QLocalMarkedJoinedCofactor.deposit
    (fun l=>a.each l U) (fun r=>Poly.send s (f r U)) z U
  have recorded (z:Key W Y):d (address K z)=D z:=funext fun U=>QLocalMarkedJoinedCofactor.on_slot K .. 
  have missing (i:ℕ) (none:i∉range (address (Y:=Y) K)):d i=0:=
    funext fun U=>QLocalMarkedJoinedCofactor.escaped K _ _ i U none
  have covers (z:Key W Y) {j:ℕ} (hj:j∈z.1.2) :
      scopes W j⊆joined W (Y z.1.1) z.1.2:=fun _ hx=>mem_union_right _ (mem_biUnion.2 ⟨j,hj,hx⟩)
  have roots (z:Key W Y) (U:Config G n) :
      Carries (fun v=>{a.origins v}) (joined W (Y z.1.1) z.1.2) (D z U):=by
    by_cases admitted:gate z U
    · change Carries _ _ (if gate z U then _ else _)
      rw [if_pos admitted]
      apply Carries.mul
      · intro h v hv out
        by_cases eq:h=s
        · subst h
          by_cases iszero:f z.1.1 U=0
          · simp [iszero]
          exact False.elim (out (Finset.singleton_subset_iff.mpr
            (mem_union_left _ (paid.roots _ U iszero v hv))))
        · simp [eq]
      · apply Carries.prod
        intro j hj h v hv out
        exact (before j).1 U h v hv (fun reach=>out (reach.trans (covers z hj)))
    · simpa [D,QLocalMarkedJoinedCofactor.deposit,admitted] using
        (carry_zero (O:=fun v=>{a.origins v}) (X:=joined W (Y z.1.1) z.1.2) (R:=Γ))
  have reader (z:Key W Y):UsesFinal W.p.threshold (joined W (Y z.1.1) z.1.2) (D z):=by
    intro U V data flag
    have sub:Y z.1.1⊆joined W (Y z.1.1) z.1.2:=Finset.subset_union_left
    have head:=paid.reads z.1.1 U V (agrees_mono data sub) (restrict_flags sub flag)
    have body:(∏j∈z.1.2,a.each j U)=(∏j∈z.1.2,a.each j V):=
      Finset.prod_congr rfl (fun j hj=>(before j).2.1 U V (agrees_mono data (covers z hj))
        (restrict_flags (covers z hj) flag))
    have guards : gate z U ↔ gate z V := by
      change (_ ∧ joined W (Y z.1.1) z.1.2 ∩ RG.flags W.p.threshold U=_) ↔
        (_ ∧ joined W (Y z.1.1) z.1.2 ∩ RG.flags W.p.threshold V=_)
      rw [flag]
    change (if gate z U then _ else _)=(if gate z V then _ else _)
    rw [propext guards]
    dsimp only
    rw [head,body]
  have gauge (z:Key W Y):GaugeInvariant (D z):=by
    intro g U
    simp only [D,QLocalMarkedJoinedCofactor.deposit,gate,gauge_flags,paid.gauge _ g U,
      fun j=>(before j).2.2.1 g U]
  have measure (z:Key W Y):Measurable (D z):=by
    by_cases h:(z.1.2:Set ℕ).Pairwise (fun i j=>Disjoint (scopes W i) (scopes W j))
    · have visible:MeasurableSet {U|gate z U}:=by
        simpa only [gate,h,true_and] using (guard_measurable (G:=G) (stock z).1.2 (stock z).1.1 W.p.threshold)
      exact (((Bands.sends s).measurable.comp (paid.measurable z.1.1)).mul
        (Finset.measurable_prod _ (fun j _=>(before j).2.2.2))).ite visible measurable_const
    · simp [D,QLocalMarkedJoinedCofactor.deposit,gate,h]
  have forces (z:Key W Y) (U:Config G n) (live:D z U≠0):
      (W.activities.forced (address K z)).eligible W.p.threshold U:=by
    have good:gate z U:=by by_contra no; exact live (by simp [D,QLocalMarkedJoinedCofactor.deposit,no])
    have flags:scopes W (address K z)∩RG.flags W.p.threshold U=inventory W (address K z):=by
      rw [(geometry K z).1,(geometry K z).2];exact good.2
    exact ⟨flags,K.pass (stock z,Encodable.encode z.1) U flags⟩
  have at_slot (i:ℕ): (∀U,Carries (fun v=>{a.origins v}) (scopes W i) (d i U)) ∧
      UsesFinal W.p.threshold (scopes W i) (d i) ∧ (∀U,d i U≠0→(W.activities.forced i).eligible W.p.threshold U) ∧
      Measurable (d i) ∧ GaugeInvariant (d i):=by
    by_cases yes:i∈range (address (Y:=Y) K)
    · obtain ⟨z,rfl⟩:=yes
      rw [recorded,(geometry K z).1]
      exact ⟨roots z,reader z,forces z,measure z,gauge z⟩
    · rw [missing i yes]
      exact ⟨fun _=>carry_zero,fun _ _ _ _=>rfl,fun _ h=>False.elim (h rfl),measurable_const,fun _ _=>rfl⟩
  exact ⟨fun i=>(at_slot i).1,fun i=>(at_slot i).2.1,fun i=>(at_slot i).2.2.1,
    fun i=>(at_slot i).2.2.2.1,fun i=>(at_slot i).2.2.2.2⟩

end YM.Integration.QLocalMarkedJoinedEligibility
