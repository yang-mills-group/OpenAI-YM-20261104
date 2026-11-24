import YM.OPE.Wefts.Pulp
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
/-! Variable group arities from shared connected touches between
markers. Representatives include the center leaf (no artificial
sources inserted in the nilpotent polynomial or layout). -/
namespace YM.OPE.Thorn
open Function Set Lattice MergeProof.Scions MergeProof.Wefts
open scoped Topology Classical
variable {sp : ℕ}
lemma graph_frame (G:SimpleGraph (Pods sp)) (ht:∃ a b,G.Adj a b):
      ∃ m < sp,∃ Δ:Divider sp m,Δ.reach pivot = pivot ∧ Δ.paint pivot = pivot ∧ ∀ a b,(G.Reachable a b ↔ Δ.paint a = Δ.paint b):=by
     let kl : Setoid (Pods sp) := ⟨G.Reachable,G.reachable_is_equivalence⟩
     let F:=Quotient kl
     let q:Pods sp→F:=Quotient.mk''; let z:F:=q pivot
     have he(a b:Pods sp): G.Reachable a b↔q a=q b:= (@Quotient.eq' _ kl a b).symm -- check
     have hq:Surjective q:= (@Quotient.mk_surjective _ kl)
     let rep(y:F):= if h:y=z then pivot else Classical.choose (hq y)
     have hr(y:F):q (rep y)= y := by
        by_cases hy:y=z
        · simp [rep,hy,z]
        simp [rep,hy,Classical.choose_spec (hq y)]
     have hcard:Fintype.card F ≤ Fintype.card (Pods sp):=Fintype.card_le_of_surjective _ hq
     rw [show Fintype.card (Pods sp)=sp+1 from Fintype.card_fin _] at hcard
     have strict:Fintype.card F ≤ sp := by
        by_contra hx
        have hs:Fintype.card F=sp+1:=by omega
        obtain ⟨a,b,H⟩:=ht; have hh:= Fintype.bijective_iff_surjective_and_card q|>.2 ⟨hq,show Fintype.card (Pods sp)=Fintype.card F from (Fintype.card_fin (sp+1)).trans hs.symm⟩; exact G.loopless.irrefl a ((hh.injective ((he a b).mp H.reachable)).symm ▸ H)
     obtain ⟨m,hm⟩:= Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α:=F)); rw [hm] at strict
     let e : F ≃ Pods m:= (Fintype.equivFin F).trans ((Equiv.cast (congr_arg Fin hm)).trans (Equiv.swap ((Equiv.cast (congr_arg Fin hm) : Fin (Fintype.card F) ≃ Pods m) ((Fintype.equivFin F) z)) (pivot:Pods m)))
     have hv : e z = pivot := Equiv.swap_apply_left ..
     let Δ:Divider sp m:=⟨e ∘ q, rep ∘ e.symm,fun i=>by simp [hr]⟩
     have hd: rep z=pivot:=by simp [rep]
     exact ⟨m, strict, Δ, (congr_arg (fun a=>Δ.reach a) hv.symm).trans ((congr_arg rep (e.symm_apply_apply z)).trans hd),hv,fun a b=> (he a b).trans e.apply_eq_iff_eq.symm⟩

section
variable {I:Type*} {n:Side} [Fintype I] (G:SimpleGraph I) (u:I→Site n) (d:ℕ) {i j:I}
omit [Fintype I] in
lemma walk_bound (h:∀ {i j},G.Adj i j→ separation (u i) (u j) ≤ d)(w:G.Walk i j) :
        separation (u i) (u j) ≤ d*w.length := by
    induction w with
    | nil=>rw [separation_self];exact Nat.zero_le _
    | @cons i j k hej w ih=> exact (separation_triangle _ (u j) _).trans ((add_le_add (h hej) ih).trans_eq (by rw [SimpleGraph.Walk.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_comm]))
lemma length_bound (h:∀ {i j},G.Adj i j→ separation (u i) (u j) ≤ d) {i j:I}(ht:G.Reachable i j):
       separation (u i) (u j)≤ d*Fintype.card I:=by
    obtain ⟨w,hw⟩:=ht.exists_isPath
    have hx:= hw.support_nodup.length_le_card
    apply (walk_bound G u d h w).trans (Nat.mul_le_mul_left _ ((Nat.le_succ _).trans _))
    simpa using hx
end
section
variable {n:Side} (d:ℕ)(u:Pods sp→Site n)
lemma cut_divider (ht:∃ a b,a ≠ b ∧ separation (u a) (u b) < d):
     ∃ m₁ < sp,∃ Δ:Divider sp m₁, Δ.reach pivot=pivot ∧
       (∀ i,separation (u (Δ.reach (Δ.paint i))) (u i) ≤ d*(sp+1)) ∧ ∀ a b:Pods m₁,a≠b→d ≤ separation (u (Δ.reach a)) (u (Δ.reach b)):=by
     let E i j:= i≠j ∧ separation (u i) (u j) < d
     let G:=SimpleGraph.mk E ⟨fun a b h=>⟨h.1.symm,separation_comm _ _ ▸ h.2⟩⟩ ⟨fun i h=>h.1 rfl⟩
     obtain ⟨m₁,hm,Δ,h₁,h₂,h₃⟩:=graph_frame G ht
     have h (i):=length_bound G u d (fun h=> h.2.le) ((h₃ (Δ.reach (Δ.paint i)) i).mpr (Δ.lands _)); rw [show Fintype.card (Pods sp)=sp+1 from Fintype.card_fin _] at h
     exact ⟨m₁,hm,Δ,h₁,h,fun a b hab=> le_of_not_gt (fun h=>hab (((Δ.lands _).symm).trans (((h₃ _ _).mp (SimpleGraph.Adj.reachable (show G.Adj (Δ.reach a) (Δ.reach b) from ⟨fun h=>hab ((Δ.lands a).symm.trans ((congr_arg Δ.paint h).trans (Δ.lands b))),h⟩))).trans (Δ.lands ..))))⟩
end
end YM.OPE.Thorn
