import YM.Trace.Physicalv2.GermSplit
import YM.Extra.SOURCE_HISTORIES.Unit
/-! # Harvest inputs properties in one Family. Thin interface (later Gear implements explicitly)

Deduplicate weld reports per j,d through whole horizon. Doesn't discard wraps, no reroll of finite pages.
-/
set_option autoImplicit false
set_option maxHeartbeats 640000
noncomputable section
namespace YM.SignedWilsonExpansion.Purchases
open Function Filter Matrix Lattice RG Wilson Gauge Extra.Histories Analysis
open Source Labels Trace.Physical.Germ Trace.Physical.GermGraph
open scoped Classical ContDiff BigOperators
variable {G:Gauge} {d i j l b n c N p r h:ℕ}{C:Family G}{F:Frame G d}
-- exact '
local notation "F₀" => (C.labels.level d)
local notation "H₀" => C.path
abbrev lives (C:Family G)(d N p b n:ℕ) (P:∀ i, Voice (C.labels.level d) C.path p i):Prop:= ∀ k∈ Finset.Icc b (b+n), Heard (C.localSection d) C.path N p C.params k (P k)
def blastCurve (C:Family G) (d N p b:ℕ): (n:ℕ)→ (Config G (C.side (b+n) p)→ℂ) → Config G (C.side b p)→ℂ
  | 0,f=>f
  | n+1,f=> blastCurve C d N p b n (blast C.path N p (b+n) d f)
def signalQ (C:Family G)(d N p j n:ℕ)(w:C.label d): Config G (C.side j p)→ℂ := blastCurve C d N p j n ((primary 0 w).density 0 (C.localSection d) (C.path.rep N p (j+n)))
structure PurchVoice (C:Family G) (d N p j n:ℕ) where
    path : ∀ i, Voice (C.labels.level d) C.path p i
    bought: lives C d N p j n path
    blast_step (k:ℕ)(h:k∈ Finset.Ico j (j+n)) (v: C.label d):
        ((path k).plays v).density 0 (C.localSection d) (C.path.rep N p k) = blast C.path N p k d (((path (k+1)).plays v).density 0 (C.localSection d) (C.path.rep N p (k+1)))
    startsQ (v) : (path (j+n)).plays v= primary 0 ((path (j+n)).index v)
abbrev ReceivesQ (C:Family G) (d N p j n:ℕ) (A:C.label d≃ₗ[ℂ]C.label d) : Prop:= ∀ e, ∃ (w:Coefficient (C.labels.level d) (C.side j p))(ε:ℝ), page d p j (C:=C) w=e ∧ reads d N p j w (C:=C) ε ∧ value d N p j w=signalQ C d N p j n (A.symm e)
abbrev tollQ(C:Family G)(d j p:ℕ): ℝ:= invoice (C:=C) d j p*(stock C j)
open Work.G08
namespace PurchVoice
variable (P:PurchVoice C d N p j n)
abbrev charges (k:ℕ)(v:C.label d):C.label d:= (P.path k).index v
abbrev finalX (w:C.label d): C.label d:= (P.path (j+n)).index.symm w
abbrev pollAt (w:C.label d): C.label d:= P.charges j (P.finalX w)
lemma terminal (w:C.label d) : signalQ C d N p j n w = value d N p j ((P.path j).plays (P.finalX w)):=by
    let v:= P.finalX w; let Λ(k):=(P.path k).plays v; unfold signalQ; rw [← show (P.path (j+n)).index (P.finalX w)=w from LinearEquiv.apply_symm_apply _ _] 
    -- simplifies finalX replacement rhs
    rw [← P.startsQ,LinearEquiv.apply_symm_apply] -- likely wrong
    have ht (i:ℕ)(h:i≤n): blastCurve C d N p j i (value (C:=C) d N p (j+i) (Λ (j+i))) = value (C:=C) d N p j (Λ j):=by
        induction i with
        | zero=> rfl
        | succ i ih=> rw [blastCurve, show blast C.path N p (j+i) d (value (C:=C) d N p (j+(i+1)) (Λ (j+(i+1)))) = value (C:=C) d N p (j+i) (Λ (j+i)) from (P.blast_step (j+i) (Finset.mem_Ico.mpr ⟨by omega,by omega⟩) v).symm]; exact ih (by omega)
    apply ht n le_rfl
lemma poll_exact {A:C.label d≃ₗ[ℂ] C.label d}(e:ReceivesQ C d N p j n A)(g:C.Makes)(h:j+n≤N)(ht:C.ref d≤j)(w:C.label d) : page (C:=C) d p j ((P.path j).plays (P.finalX w))=A w:=by
    obtain ⟨Q,r,hQ,hp,hE⟩:=e (A w)
    have hj:=Finset.mem_Icc.mpr (show j≤j ∧ j≤j+n from ⟨le_rfl,Nat.le_add_right ..⟩); rw [LinearEquiv.symm_apply_apply,P.terminal] at hE; exact (same_page g (by omega) ht ((P.bought _ hj).earns _) hp (EventuallyEq.of_eq hE.symm)).trans hQ
open Motion
lemma phasePoll (s:Motion)(w): P.pollAt (Extra.Histories.Motion.patch F₀ s w) = Extra.Histories.Motion.patch F₀ s (P.pollAt w):=by
    have hf: P.finalX (Extra.Histories.Motion.patch _ s w)=Extra.Histories.Motion.patch _ s (P.finalX w):=by apply (P.path (j+n)).index.injective; rw [←(P.bought (j+n) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)).moves]; unfold finalX; rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
    unfold pollAt; rw [hf]; exact ((P.bought j (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)).moves ..).symm
/-- PollAt has storage size in terms of full j page (for Arrived walk only). -/
structure ReadyReturn (C:Family G)(d N p j n:ℕ)(A:C.label d≃ₗ[ℂ] C.label d): Prop where
    pay : ReceivesQ C d N p j n A
    late : Opened C d j p
    age : j+n ≤ N
lemma yearn (g:C.Makes) {A:C.label d≃ₗ[ℂ] C.label d}(h: ReadyReturn C d N p j n A)(w:C.label d):
    (F₀).coeffSize (A w-P.pollAt w) ≤ tollQ C d j p*(F₀).coeffSize (P.pollAt w):=by
      let jz:= Finset.mem_Icc.mpr (show j≤j∧j≤j+n from ⟨le_rfl,Nat.le_add_right ..⟩); let t:= P.bought j jz; rw [←P.poll_exact h.pay g h.age h.late.post]; have hp:= measured_diff d N p j g h.late.post ((Finset.mem_Icc.mp jz).2.trans h.age) (t.earns (P.finalX w)); rw [t.currents] at hp; exact hp.trans ((mul_le_mul_of_nonneg_left ((t.cone _).trans (mul_le_mul_of_nonneg_left (size_core ..) (zero_le_one.trans ((stage C j).columns_ge)) )) (invoice_nn _ _ _)).trans_eq (mul_assoc _ _ (F₀|>.coeffSize (P.pollAt w))).symm)
lemma gruesome (g:C.Makes) {A:C.label d≃ₗ[ℂ] C.label d}(h: ReadyReturn C d N p j n A)(w:C.label d):
    (F₀).coeffSize (P.pollAt w) ≤ 2*(F₀).coeffSize (A w):= by
    have hp:= P.yearn g h w; have hs:= (size_triangle F₀ (P.pollAt w) (A w)); rw [size_sub_rev] at hs; have hv:tollQ C d j p≤1/4:= h.late.small.le; nlinarith only [hp,hs,mul_le_mul_of_nonneg_right hv (size_nonneg F₀ (P.pollAt w)),size_nonneg F₀ (P.pollAt w)]
include P
lemma unit_touch (g:C.Makes){A:C.label d≃ₗ[ℂ] C.label d}(h:ReadyReturn C d N p j n A) : A (unitVec F₀ C.path (j+n))=unitVec F₀ C.path j:= by
    let w:= unitVec F₀ C.path N; let t:= P.bought j (Finset.mem_Icc.mpr ⟨by omega,by omega⟩); have hh:P.finalX (unitVec F₀ C.path (j+n))=w:=by rw [←(P.bought (j+n) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)).unit]; exact LinearEquiv.symm_apply_apply ..
    rw [←P.poll_exact h.pay g h.age h.late.post, hh]; have hp:= measured_diff d N p j g h.late.post ((Nat.le_add_right ..).trans h.age) (t.earns w); rw [t.currents,t.unit] at hp
    have heq:(P.path j).charge w ≤ 0:= (t.cone w).trans_eq (by rw [t.unit]; simp [unitVec,map_smul,Size.unit_core,Frame.coeffSize])
    exact sub_eq_zero.mp (size_separates _ _ (hp.trans (mul_nonpos_of_nonneg_of_nonpos (invoice_nn ..) heq)))
end PurchVoice
end YM.SignedWilsonExpansion.Purchases
