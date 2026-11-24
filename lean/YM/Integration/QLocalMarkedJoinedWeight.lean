import YM.Integration.QLocalThermalTokenTariff
import YM.Integration.QLocalMarkedJoinedLinear

/-! Transfer the tariff from all signed touching pairs to their actual
reserved compulsory slots, preserving one common bound before the tested
configuration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalMarkedJoinedWeight
open Function Finset Set Lattice RG Wilson Marker Overlay Extra.Histories Planned.GuardedAtom
open RG3.Script.Picnic Push.AbsoluteSums MergeProof.Accent Push.GridApprox.Nil
open ActualWilsonTaylorSlot ActualWilsonJoinedCofactor ActualWilsonTouchingVacuum ActualWilsonDirtyPartners
open scoped Classical BigOperators
variable {X:Type*} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {G:Gauge} {n:Side} {W:Rep G n}
    {Y:ℕ→Support n} {w:V→ℝ} (hw:∀v,0<w v)

include hw

omit [Fintype V] in
theorem group (v:ℕ→Poly Γ) (b:ℕ→ℝ) (pay:∀i,Poly.price w (v i)≤ b i) (S:Finset ℕ) :
    Poly.price w (∏i∈S,v i)≤∏i∈S,b i := by
  induction S using Finset.induction_on with
  | empty=>simp
  | @insert i S hi ih=>
    rw [Finset.prod_insert hi,Finset.prod_insert hi]
    exact (Poly.multiplication hw ..).trans (mul_le_mul (pay i) ih
      (Poly.nonnegative hw _) ((Poly.nonnegative hw (v i)).trans (pay i)))

omit [Fintype V] in
theorem sheets (F:X→Poly Γ) {b:ℝ} (hb:0≤ b) (paid:∀z,Poly.price w (F z)≤ b) :
    Loci w F ((Fintype.card Γ.Mode:ℝ)*b) := by
  refine ⟨fun s=>b/Poly.toll w s,fun s=>div_nonneg hb (Poly.worth hw s).le,?_,?_⟩
  · intro z s
    apply (le_div_iff₀ (Poly.worth hw s)).mpr
    rw [mul_comm]
    exact (Poly.member hw s _).trans (paid z)
  · have restore (s:Γ.Mode):Poly.toll w s*(b/Poly.toll w s)=b:=by
      field_simp [(Poly.worth hw s).ne']
    simp [wordsPrice,restore,nsmul_eq_mul]

structure Coupon (p:BudgetPoint) (F:ℕ→X→Poly Γ) (w:V→ℝ) (W:Rep G n) (c:ℝ) where
  major : ℕ→ℝ
  nonnegative i : 0≤ major i
  field i z : Poly.price w (F i z)≤ major i
  full : SumBudget (fun i=>p.mass (ActualWilsonPacketSplit.scopes W i) (major i)) c

omit [Fintype V] in
theorem weights (p:BudgetPoint) (K:Guard.Keeper W.p W.activities) (A:X→Bands Γ W)
    (s:Γ.Mode) (f:X→ℕ→ Config G n→ℂ) (stem b:ℕ→ℝ) (c:ℝ)
    (positive:∀i,0 ≤ stem i) (old:∀i,0≤ b i ∧ ∀z:X×Config G n,Poly.price w ((A z.1).each i z.2)≤ b i)
    (head:∀i x U,Poly.toll w s*‖f x i U‖ ≤ stem i)
    (money:SumBudget (fun t:ℕ×Finset ℕ=>stem t.1*dirty p (ActualWilsonPacketSplit.scopes W) (Y t.1) b t.2) c) :
    Nonempty (Coupon p
      (fun i (z:X×Config G n)=>QLocalMarkedJoinedLinear.addition (Y:=Y) K (A z.1) s (f z.1) i z.2)
      w W c) := by
  let e:=address (Y:=Y) K
  let u (z:Key W Y):=stem z.1.1*(∏j∈z.1.2,b j)
  let y:=Function.extend e u (fun _=>0)
  have hon (z:Key W Y):y (e z)=u z:=e.injective.extend_apply ..
  have hoff i (hi:i∉range e):y i=0:=extend_apply' _ _ _ hi
  have uq (z:Key W Y):0≤ u z:=mul_nonneg (positive _) (Finset.prod_nonneg fun j _=>(old j).1)
  have yy i:0≤ y i:=by
    by_cases present:i∈range e
    · obtain ⟨z,rfl⟩:=present; rw [hon]; exact uq z
    · rw [hoff _ present]
  have point i (z:X×Config G n):Poly.price w (QLocalMarkedJoinedLinear.addition (Y:=Y) K (A z.1) s (f z.1) i z.2)≤ y i:=by
    by_cases present:i∈range e
    · obtain ⟨k,rfl⟩:=present
      rw [hon,QLocalMarkedJoinedLinear.addition,QLocalMarkedJoinedCofactor.on_slot,QLocalMarkedJoinedCofactor.deposit]
      split
      · apply (Poly.multiplication hw ..).trans
        apply mul_le_mul _ (group hw _ b (fun j=>(old j).2 z) k.1.2)
          (Poly.nonnegative hw _) (positive _)
        simpa only [Poly.solo] using head k.1.1 z.1 z.2
      · simpa using uq k
    · rw [QLocalMarkedJoinedLinear.addition,QLocalMarkedJoinedCofactor.escaped K _ _ _ _ present,hoff _ present]
      simp
  let bill i:=p.mass (ActualWilsonPacketSplit.scopes W i) (y i)
  have pos i:0≤ bill i:=(yy i).trans (p.loMass _ _ (yy i))
  have hbill (z:Key W Y):bill (e z)=p.mass (ActualWilsonPacketSplit.joined W (Y z.1.1) z.1.2) (u z):=by
    dsimp only [bill]; rw [hon,(geometry K z).1]
  have hzero i (hi:i∉range e):bill i=0:=by simp [bill,BudgetPoint.mass,hoff i hi]
  have covered:SumBudget (fun z:Key W Y=>p.mass (ActualWilsonPacketSplit.joined W (Y z.1.1) z.1.2) (u z)) c:=by
    convert budget_pull (Subtype.val:Key W Y→ℕ×Finset ℕ) Subtype.val_injective money using 1
    funext z
    simp only [dirty,if_pos z.2.1.ne_empty,invoice,if_pos z.2.2,
      u,ActualWilsonPacketSplit.joined,BudgetPoint.mass]
    ring
  have hsum:Summable (bill ∘ e):=by simpa only [Function.comp_def,hbill] using covered.2.1
  have total:SumBudget bill c:=by
    refine ⟨pos,(e.injective.summable_iff hzero).mp hsum,?_⟩
    rw [←e.injective.tsum_eq (show Function.support bill⊆range e from fun i hi=>by
      by_contra bad; exact hi (hzero i bad))]
    simpa only [hbill] using covered.2.2
  exact ⟨⟨y,yy,point,total⟩⟩

omit [Fintype V] in
theorem Coupon.towed (p:BudgetPoint) (L:ℕ→X→Poly Γ) {c:ℝ} (lease:Coupon p L w W c) :
    Towed w (ActualWilsonPacketSplit.scopes W) L p.B p.supportExponent ((Fintype.card Γ.Mode:ℝ)*c) := by
  let y:=lease.major
  let bill i:=p.mass (ActualWilsonPacketSplit.scopes W i) (y i)
  have pos i:0≤ bill i:=(lease.nonnegative i).trans (p.loMass _ _ (lease.nonnegative i))
  let N:ℝ:=Fintype.card Γ.Mode
  have hn:0≤ N:=Nat.cast_nonneg _
  refine ⟨fun i=>N*y i,((budget_mono lease.full lease.nonnegative (fun i=>p.loMass _ _ (lease.nonnegative i))).2.1).mul_left N,?_,
    fun i=>sheets hw _ (lease.nonnegative i) (lease.field i)⟩
  intro x
  apply budget_mono (budget_scale hn lease.full)
  · intro i
    have yi:0≤y i:=lease.nonnegative i
    split <;> positivity
  · intro i
    by_cases mem:x∈ActualWilsonPacketSplit.scopes W i
    · simp only [if_pos mem,y,BudgetPoint.mass]
      ring_nf
      exact le_rfl
    · simpa only [if_neg mem,zero_mul,bill,y] using mul_nonneg hn (pos i)

omit [Fintype V] in
theorem transferred (p:BudgetPoint) (K:Guard.Keeper W.p W.activities) (A:X→Bands Γ W)
    (s:Γ.Mode) (f:X→ℕ→ Config G n→ℂ) (stem b:ℕ→ℝ) (c:ℝ)
    (positive:∀i,0 ≤ stem i) (old:∀i,0≤ b i ∧ ∀z:X×Config G n,Poly.price w ((A z.1).each i z.2)≤ b i)
    (head:∀i x U,Poly.toll w s*‖f x i U‖ ≤ stem i)
    (money:SumBudget (fun t:ℕ×Finset ℕ=>stem t.1*dirty p (ActualWilsonPacketSplit.scopes W) (Y t.1) b t.2) c) :
    Towed w (ActualWilsonPacketSplit.scopes W)
      (fun i (z:X×Config G n)=>QLocalMarkedJoinedLinear.addition (Y:=Y) K (A z.1) s (f z.1) i z.2)
      p.B p.supportExponent ((Fintype.card Γ.Mode:ℝ)*c) := by
  obtain ⟨lease⟩:=weights hw p K A s f stem b c positive old head money
  exact Coupon.towed hw p _ lease

end YM.Integration.QLocalMarkedJoinedWeight
