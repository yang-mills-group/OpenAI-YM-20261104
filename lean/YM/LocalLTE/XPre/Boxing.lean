import YM.LocalLTE.XPre.Trunk
import YM.LocalLTE.XPre.Gallery
/-!
# Compressed physical columns. Applies to already-clustered offers from Family Γ at any V.
 Keeping exact `profile` costs at merger. Emits chords at exponent.Y.Lean. Does NOT replace
 with fitted marginal. Ergo Odyssey proof needed. Allows prescribing subset P for
 programming forecast ingredients. Preserve occupants when too expensive.E*.Supplementary
 log jobs emitted separately; no projection assumed from model.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.XPre
open Function Finset Filter Set MeasureTheory Lattice Wilson RG
open Extra.Histories Push Local Motion Extra.Multi
open LocalLTE.Fan LocalLTE.River LocalLTE.Vinca Ticket
open PhysicalNext.Repeat Lotus Blush Progress.DirectedRecipe
open YM.MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{c f:Side}{S:StepData c f} {R : Rep G f} {C: Rep G c}
variable {J:Type}[DecidableEq J][Fintype J]
variable (B:Marker.Census J){d p l:ℕ} {κ w a:ℝ}
open Menu Marker Accent
variable (F:J→ Config G f→ℂ)(Z:J→ Res G f)(W:J→ Res G c)(ψ:J→ℂ) (R': J→ℝ) (hr:∀ i,0<R' i)
    (D:GaugeDoor R C)(o:J→Site f)(b:J→Site c)(t v u:J→ℝ)
-- rank for each all in finite cost.Integer uniform d.S.
variable (h:∀ i,∃ X:Set Wing,X.Finite∧ Circuit X D d κ p l (o i) (b i) 1 (F i) (Z i) (W i) (ψ i) (t i) (v i) (u i))
variable (hs:SoundDoor S D)(ht:Tunes D)
variable (Y:J→ℝ)(hy:∀ i,0<Y i)
include h hr hs ht hy
set_option quotPrecheck false
lemma rally : ∃ (ϕ : J→ MergeProof.Response G c),(∀ i,Attainment C.p (b i) (ϕ i) (v i)) ∧ ∃ (I N:Type) (_:Fintype I)(_:Fintype N)(P:I→Menu.Hat B R)(A:N→Menu.Hat B R), let M:= Sum.elim P A
      (∀ i:(I⊕N),(M i).s.val.image o⊆(M i).M.crest)∧(∀ i,XPre.Reader R d κ p l (P i|>.M))∧(∀ U, Menu.roll M U=Mach B (fun i=> F i U-ψ i))∧(∀ i U,Menu.board M i U=Mach B (fun j=> Z j i U))∧(∀ i j U,(∑ k, Menu.owl (M k) D j i U)=W j i U - hook C.activities C.p.threshold (ϕ j) i U)∧(∑ i:I,R.p.mass ((P i).M.crest) (Menu.fare (P i) R')) ≤ ∑ j:J,R' j*t j ∧ (∑ i:N,R.p.mass ((A i).M.crest) (Menu.fare (A i) R')) ≤ ∑ j:J, 2*R' j*(u j+Y j) :=by
    choose X hX ι hι Q U Fun A hr' hb hx using fun i => (show ∃ X:Set Wing,X.Finite∧ ∃ (lx:Type)(_ : Countable lx) (M:lx→ Lotus.Leaf R)(g:lx→ℂ)(ϕ:MergeProof.Response G c)(A:lx→Prop), Odyssey X (o i) (b i) 1 (F i) (Z i) (W i) (ψ i) (t i) (v i) D M g ϕ ∧ SumBudget (tollNon A M g) (u i) ∧ ∀ z,A z→ Reader R d κ p l (M z) from (by obtain ⟨X,h,hx⟩:= h i; exact ⟨X,h,hx.lamps⟩))
    · -- fix l binder
      choose V hV using fun i=>tailless (hr' i).purchase (hy i)
      choose I hI N hN hW hP hU hE hO hT using fun i=> munition (V i) (hr' i) (A i) (hb i) B i R' hr (hx i) (Y i) hs ht (hX i) (hV i)
      let ξ (i:J):Type := ↥((V i).filter fun j=>A i j); letI fi(i):Fintype (ξ i):=inferInstanceAs (Fintype (↥((V i).filter fun j=> A i j)))
      let H i (j:ξ i):= active B (Q i) (U i) i j.val
      let P:= Sigma.uncurry H; let Q' := Sigma.uncurry N; let Xt:=Sum.elim P Q'
      refine ⟨Fun,fun i=> (hr' i).cost,Sigma ξ,Sigma I, inferInstance,inferInstance,P,Q',?_,?_,?_,?_,?_,?_,?_⟩
      · rintro (i|i)
        · change (P i).s.val.image o ⊆ _; have he := hN i.1 (.inl i.2); simp only [show (P i).s=B.fire i.1 from he.1,Census.fire,Finset.image_singleton,Finset.singleton_subset_iff]; exact he.2
        change ((Q' i).s.val.image o ⊆ _); have he := hN i.1 (.inr i.2); simp only [show (Q' i).s=B.fire i.1 from he.1,Census.fire,Finset.image_singleton,Finset.singleton_subset_iff]; exact he.2
      · intro i; exact hW i.1 (.inl i.2) rfl
      · intro x
        rw [Menu.perfumes, Fintype.sum_sum_type, Fintype.sum_sigma,Fintype.sum_sigma, ← Finset.sum_add_distrib] -- name
        refine Finset.sum_congr rfl fun j _=>?_ ; have hp':= hE j x; rw [Fintype.sum_sum_type] at hp'; exact hp'
      · intro i U'; rw [Menu.patron,Fintype.sum_sum_type,Fintype.sum_sigma,Fintype.sum_sigma,← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _=> ?_; have hx:= hO j i U'; rw [Fintype.sum_sum_type] at hx; exact hx
      · intro i j V; rw [Fintype.sum_sum_type,Fintype.sum_sigma,Fintype.sum_sigma,← Finset.sum_add_distrib,sum_eq_single j]
        · have hx:= hT j i V; rw [Fintype.sum_sum_type] at hx; exact hx
        · intro b _ hb; have hp(j':Σ i,ξ i):= hN j'.1 (.inl j'.2); have hkz:B.fire b≠ B.fire j:=(B.fire_inj ..).not.mpr hb; change (∑ c:ξ b, owl (P ⟨b,c⟩) _ _ _ _) + (∑ c:I b, owl (Q' ⟨b,c⟩) _ _ _ _) = _
          rw [Finset.sum_eq_zero (f:=fun c:ξ b=> owl (P ⟨b,c⟩) D j i V) (fun i _=> if_neg hkz ), Finset.sum_eq_zero (f:=fun c:I b=> owl (Q' ⟨b,c⟩) D j i V) (fun i _=> ?_),zero_add]
          exact if_neg fun h=> hkz ((hN b (.inr i)|>.1).symm.trans h)
        simp
      · rw [Fintype.sum_sigma]; exact Finset.sum_le_sum fun i _=> hP i
      rw [Fintype.sum_sigma]; exact Finset.sum_le_sum fun i _=> hU i
end YM.LocalLTE.XPre
