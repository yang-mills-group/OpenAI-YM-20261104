import YM.Contacts.Sentry.Observe
import YM.Contacts.Costar.Valet
import YM.Contacts.Costar.Offset
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Sensor
open Function Set Filter MeasureTheory Extraction Lattice Cells Wilson Word Costar Bid Next.Phase
open scoped Topology BigOperators
variable {G:Gauge} {L:Register G}{C:Family G}
variable {ι J : Type} [Fintype ι][Fintype J]{k:ℕ}{τ:Filter (ℕ×ℕ)}
-- Couple inputs to cutoff or reference. Varying exterior parameters independent.
structure MatchToken (C:Family G) (τ:Filter (ℕ×ℕ)) where
    token : C.book.Token
    v : ℕ×ℕ→ C.label token.1
    tends : Tendsto v τ (𝓝 token.2)
structure Ballot (C:Family G) (k : ℕ) (τ:Filter (ℕ×ℕ)) where
    I : Type
    [fin : Fintype I]
    u : I → Cover
    s : I → MatchToken C τ
    clear : clear _ (C.S.gridPoint k ∘ u)
    weight : ℂ
attribute [instance] Ballot.fin
variable {n:ℕ}(A: Fin n → Ballot C k τ)

def MatchToken.stays (w : C.book.Token) : MatchToken C τ:=⟨w,fun _=>w.2,tendsto_const_nhds⟩
@[simp] lemma MatchToken.stays_token (w : C.book.Token) : (MatchToken.stays (C:=C) (τ:=τ) w).token=w:=rfl
variable (F:Extraction.Order)
def arrives : Episode C F k where
     num:=n; factor i:=(A i).weight; image i:=Fintype.card (A i).I
     seats i:=(A i).u ∘ (Fintype.equivFin (A i).I).symm
     gen i:= clear_maps (A i).clear (Fintype.equivFin (A i).I).symm.injective
     weight i j:= ((A i).s ((Fintype.equivFin (A i).I).symm j)).token.1
     point i j:= ((A i).s ((Fintype.equivFin (A i).I).symm j)).token.2
     current i j _ _:= ((A i).s ((Fintype.equivFin (A i).I).symm j)).token.2
     views i j:=⟨(by simp),fun _=> ((A i).s ((Fintype.equivFin (A i).I).symm j)).token.2,fun _ _=> tendsto_const_nhds,tendsto_const_nhds⟩
def voted : Ticket (arrives A F) τ where
     current i j N p:= ((A i).s ((Fintype.equivFin (A i).I).symm j)).v (N,p)
     tends i j:= ((A i).s ((Fintype.equivFin (A i).I).symm j)).tends

def Ballot.vote (a:Ballot C k τ)(N p:ℕ)(U : Config G (C.side N p)):= a.weight*∏ i, C.O N p (((a.s i).v (N,p))) (location C.S k N p (a.u i)) U
def Ballot.observe (S:Table C.book)(a:Ballot C k τ):= a.weight* sample S (C.S.gridPoint k ∘ a.u) (MatchToken.token ∘ a.s)
lemma ballot_vote (N p:ℕ) : (voted A F).cuts N p 0= ∑ i:Fin n,(A i).vote N p:=by
    ext1 x; simp only [Ticket.cuts, add_zero]; change ∑ i:Fin n, _= _; rw [Finset.sum_apply]; apply Finset.sum_congr rfl; intro i _
    apply congr_arg ((A i).weight*·); exact Equiv.prod_comp (Fintype.equivFin (A i).I).symm (fun j=> C.O N p (((A i).s j).v (N,p)) (location C.S k N p ((A i).u j)) x)
lemma tally_vote (S:Table C.book): (∑ i, (arrives A F).factor i* S.expect ((arrives A F).word i))= ∑ i:Fin n,(A i).observe S:=by
    unfold Episode.word; simp_rw [Table.readAt]; rfl
variable [τ.NeBot]{F}
open Org Spec
lemma stands (hT:τ ≤ F.fuse){S : Table C.book}(V:Final C F S
   )(hp:Grill C F) (v:Viewer V) {b l t:ℕ}(e:b≤k)(hl:b≤l)(ht:l≤t)(w:J→ C.book.Token)(y:J→ Cover)(B:J→ℝ){D:ℝ}(hA:0≤D) (hB:∀ i,0≤ B i)
    (hgap:∀ i,2*C.S.a b< ‖C.S.gridPoint k (y i)‖)
    (hh:∀ i j,i≠j→ 2*C.S.a l < ‖C.S.gridPoint k (y i)-C.S.gridPoint k (y j)‖) (hs:∀ i, F.late (Single C (w i) (B i) t))
    (ht': ∀ᶠ c:ℕ×ℕ in τ, ∃ (o:Site (C.side c.1 c.2)) (Z:Config G (C.side c.1 c.2)→ℂ) (he:k ≤ c.1) (hY:t ≤ c.1),
       let T:= (center C.S c.2 (e.trans he) 0).newly o; let L:= (center C.S c.2 (ht.trans hY) 0).newly o;
       0∈ T.chamber 0 ∧ Interior (T.chamber 0) Z ∧ T.rootTest (C.beta c.1 c.2) Z ≤ D ∧
       (∀ i, Next.Phase.Inside L (3*span C.S hY c.2) (location C.S k c.1 c.2 (y i))) ∧
         (∑ i,(A i).vote c.1 c.2) = fun U=> Z U*∏ i,C.seen (w i) (location C.S k c.1 c.2 (y i)) U):
     ‖∑ i:Fin n,(A i).observe (watches V v)‖ ≤ D*∏ i,B i:=by
   rw [← tally_vote A F]
   let p:=(Fintype.equivFin J).symm; rw [← Equiv.prod_comp p]; refine follow (voted A F) e hl ht D (w ∘ p) (y ∘ p) (B ∘ p) hT V hp v hA (fun i=>hB _) (fun i=> hgap _) (fun _ _ h => hh _ _ (p.injective.ne h)) (fun i=> hs _) ?_
   apply ht'.mono; rintro c ⟨o,Z,he,hY,hD,hZ,hp,hW,hC⟩; refine ⟨o,Z,he,hY,hD,hZ,hp,(fun i=> hW _),?_⟩; rw [ballot_vote,hC]; ext1 U
   exact congr_arg (Z U*·) (Equiv.prod_comp p (fun i=>C.seen (w i) (location C.S k c.1 c.2 (y i)) U)).symm
end YM.Contacts.Sensor
