import YM.GradedFar.Physical.ScaleMeter
import YM.OPE.Sparse.Erase

/-!
# Synchronized unit deletion for moving true calls on actual fields (proc)
 Extra projections for preserving conventions into the continuum test & M.3
 etc. This does not introduce any change of test. Not a statement about cutoff processing.
 It uses the literal continuum `Sparse` and `Table` as in that proof.
-/
namespace YM.FVA2.GradedFar.Physical.Literal
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open OPE Orbits Logged Nesting
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m n' m' d h k : ℕ}
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (K : FramesH P)
    (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (simple:G.Simple) (hk:oriented U K)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
open GradedFar.Subarray
variable (a:Fin n' ↪ Fin n)(b:Fin m'↪Fin m)(d:Fin n→ℕ)(e:Fin m→ℕ)
lemma all_face (w:Continuation.Window) (i:View U)(x: Points n)(y:Points m)(u:Inputs G d)(v:Inputs G e)(s t:ℝ)
    (hx0: Injective (beside (atPos w.len i.2 x) (atPos w.Coarse i.2 y)))
    (hx:∀ j∉range a, here K s u j=P.unit (d j))(hy:∀ j∉range b, here K t v j=P.unit (e j)) :
     whole (spectator U i.1) (atPos w.len i.2 x) (here K s u) (atPos w.Coarse i.2 y) (here K t v)=
     whole (spectator U i.1) (atPos w.len i.2 (config a x)) (here K s (tuple a u)) (atPos w.Coarse i.2 (config b y)) (here K t (tuple b v)) := by
    let E:= Sum.map a b; let big:= Orbits.tags (stages (here K s u) (here K t v)); let z:=beside (atPos w.len i.2 x) (atPos w.Coarse i.2 y)
    let small:= Orbits.tags (stages (here K s (tuple a u)) (here K t (tuple b v))); let z':=beside (atPos w.len i.2 (config a x)) (atPos w.Coarse i.2 (config b y))
    have he j (h:∀ t,E t≠j) : Sparse.literal (big j) := by
       rcases j with j|j
       · exact hx j (fun ⟨t,ht⟩=>h (.inl t) (congrArg Sum.inl ht))
       exact hy j (fun ⟨t,ht⟩=>h (.inr t) (congrArg Sum.inr ht))
    have hf:= Sparse.Undo.restrict (Sparse.momentIdentity (S:=P) (spectator U i.1) (spectate U i.1) (spectate_respects U i.1)) z hx0 E (a.injective.sumMap b.injective) big he
    change moment (spectator U i.1) _ _= moment (spectator U i.1) (z ∘ E) (voices (big ∘ E)) at hf
    rw [show z ∘ E=z' from funext fun i=>by cases i <;> rfl,show big ∘ E=small from funext fun i=>by cases i <;> rfl] at hf
    exact hf
lemma packet_face (r:ℝ)(i:View U)(x:Points n)(u:Inputs G d)(h:ℕ) (hx:∀ j∉range a, here K r u j = P.unit (d j))
    (hs:∀ j≤h, orbitMargin Q.port j (atPos r i.2 x) i.2) : packet U K Q d h r i x u= packet U K Q (d ∘ a) h r i (config a x) (tuple a u) := by
    apply congrArg (K r h).symm; unfold Reader.packet; refine Finset.sum_congr rfl fun j _=> congrArg (U.sector.derivatives.rise (Nat.le_of_lt_succ j.isLt)) ?_
    let V:= Orbits.tags (here K r u); have he i (h:∀ j,a j ≠ i) : Sparse.literal (V i):= hx _ (fun ⟨b,hb⟩=>h b hb)
    exact Sparse.Undo.restrict (Sparse.readingIdentity U Q i.2 _) _ (hs j.val (Nat.le_of_lt_succ j.isLt)) a a.injective V he
variable (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {B C : ℝ} (hB:0<B)(hC:0<C)
include H hB hC hk
set_option linter.unusedSectionVars false in
/-- Can apply with same correspondence and bounds in Elected, including comparison in any
     spectral phase, remaining n'>0 for the `S` OPE in M.3. Actually works for all n'
     in this compatibility assertion. No varying the price threshold with the requested
     ordering. Use `Yx_mask` and `vector_mask` & `responses_eq` for the formal part as
     always. Uses height and radius budget as in M.3. -/
theorem full_agreement {X:Set (Points n)} {Y:Set (Points m)} (hX:IsCompact X)(hx:X⊆conf n)(hY:IsCompact Y)(hy:Y⊆ O.Enh.Outside m)(h:ℕ):
    ∀ᶠ (w:Continuation.Window) in windows (upper G C B),
      ∀ x∈X,∀y∈Y,∀ (u:Inputs G d) (v:Inputs G e), (∀i∉range a, u i=leaf G (d i)) →
       (∀ i∉range b,v i=leaf G (e i)) → ∀ i:View U,
       let X':=config a x; let Y':=config b y; let U':=tuple a u; let V':=tuple b v
       Ywide U K w i x y u v= Ywide U K w i X' Y' U' V' ∧ (∀ p':Sec G h,
           Dwide U K w i y v p' = Dwide U K w i Y' V' p') ∧
           packet U K Q d h w.len i x u=packet U K Q (d ∘ a) h w.len i X' U' := by
    let Y0:Set (Points 1):={0}; have h0:Y0 ⊆ conf 1:= singleton_subset_iff.mpr fun i j h=> Subsingleton.elim ..
    have he:=coarse_motion simple hC hB; let k:= upper G C B
    filter_upwards [Tasks.entitled hX hx hY hy k, Tasks.entitled isCompact_singleton h0 hY hy k,
      he.eventually (eventually_all.mpr (fun i : Fin m=> hk.unit (e i))), (windows_short k).eventually (eventually_all.mpr (fun i: Fin n => hk.unit (d i))),
      (windows_short k).eventually (Tasks.booked_margins U Q hX hx h)] with w hh h0 h1 h2 hq x hx y hy u v hu hv i X' Y' U' V'
    have hf j (h:j ∉ range a) : here K (Window.len w) u j=P.unit (d j) := by unfold here; rw [hu j h, h2 j]
    have he j (h:j ∉ range b) : here K (Window.Coarse w) v j=P.unit (e j) := by unfold here; rw [hv j h, h1 j]
    exact ⟨all_face U K a b d e w i x y u v _ _ (hh x hx y hy i.2) hf he,fun p'=>all_face U K (Function.Embedding.refl (Fin 1)) b _ e w i _ y (fun _=>p') v _ _ (h0 0 (mem_singleton _) y hy i.2) (fun i h=>False.elim (h ⟨i,rfl⟩)) he,
      packet_face U K Q a d (Window.len w) i x u h hf (hq _ hx i.2)⟩
end
end YM.FVA2.GradedFar.Physical.Literal
