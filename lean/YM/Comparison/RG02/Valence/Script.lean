import YM.Comparison.RG02.Valence.Pooled
/-! Occurrences weight before applying the connected recurrence. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Valence
open Function Filter Finset YM.Analysis YM.Marker YM.Multi Cumulants Cumulants.Wick
open YM.Extra.Trajectories (connected connected_quiet)
open YM.Next.Rank
open scoped Topology BigOperators Classical ContDiff

variable {V J : Type} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq V] [Fintype V] {R : Census V}
    (Q : Normal.Symmetric J) (μ : E→J→ℂ) (hμ : ∀ j, Level 1 (fun x=> μ x j))

def Core (J : Type) (n : ℕ) : Set (Normal.poly J) := {p | ∃ k ≤ n, ∃ Z : Fin k→J, p=Normal.glyphs Z univ}
def Area (J : Type) (n : ℕ) := Submodule.span ℂ (Core J n)
lemma fits (n : ℕ) (Z : Fin n→J) : Normal.glyphs Z univ∈ Area J n:=Submodule.subset_span ⟨n,le_rfl,Z,rfl⟩
lemma fits_one (n:ℕ) : 1∈ Core J n:= ⟨0,Nat.zero_le _,Fin.elim0,by simp [Normal.glyphs]⟩
include hμ
lemma drawn (t : R.Mode) (u : V→ℕ) (w : V→ Normal.poly J) (p : ℤ) (v : Finset V) (hv:v ⊆ t.val)
    (hw : ∀ i∈v,w i∈ Area J (u i)) (hc : ∀ i∈t.val,i∉v→ w i∈ Core J (u i))
    (h : (∑ i∈t.val,(u i:ℤ))+2-2*t.val.card≤p) : Level p (fun x=> (connected (moments R (Normal.blend Q (μ x)) w)).part t) := by
   let a (w:V→ Normal.poly J) (x:E) := (connected (moments R (Normal.blend Q (μ x)) w)).part t
   induction v using Finset.induction generalizing w with
   | empty=>
     let b(i:V):= if i∈t.val then w i else 1
     have hb(i:V): b i∈Core J (u i):= by unfold b; split_ifs with hi; exact hc i hi (notMem_empty _); exact fits_one _
     choose k hk Z hZ using (show ∀ i,∃ k≤ u i,∃ Z:Fin k→J, b i=Normal.glyphs Z univ from hb)
     have he:= funext hZ
     change Level p (a w); have hh:a w=a b:= funext fun x=> equal_occurrences (Normal.blend Q (μ x)) w b t (fun i hi=> (if_pos hi).symm)
     rw [hh,he]; apply price_list Q μ hμ
     refine le_trans ?_ h; gcongr; apply hk
   | insert s V he IH =>
     let c z := a (update w s z)
     have hs := hv (mem_insert_self ..); let L(x:E) := rootCumulant (Normal.blend Q (μ x)) (Normal.fresh ..) w s hs
     suffices hp : ∀ z∈Area J (u s), Level p (c z) by
        have hz:=hp _ (hw s (mem_insert_self ..)); change Level p (a w); rwa [show c (w s)=_ from congrArg a (update_eq_self s w)] at hz
     intro z hz; induction hz using Submodule.span_induction with
     | mem z hz=>
       unfold c a; apply IH _ (fun _ hi=>hv (mem_insert_of_mem hi)) (fun i hi=>?_) (fun i hi hk=>?_)
       · rw [update_of_ne (ne_of_mem_of_not_mem hi he)]; exact hw i (mem_insert_of_mem hi)
       by_cases hp:i=s; · rw [hp,Function.update_self]; exact hz
       rw [update_of_ne hp]; exact hc i hi (by simp [hp,hk])
     | zero=>
       change Level p (fun x=> L x 0); simp_rw [map_zero]; exact Level.zero _
     | add v v' hv hv' h H=>
       change Level p (fun x=> L x (v+v')); simp_rw [map_add]; apply Level.add; exact h; exact H
     | smul x v hv H=>
       change Level p (fun y=> L y (x • v)); simp_rw [map_smul,smul_eq_mul]; exact H.factor x

lemma full (t : R.Mode) (u : V→ℕ) (w : V→ Normal.poly J) (p : ℤ)
    (hw : ∀ i∈t.val,w i∈ Area J (u i))
    (h : (∑ i∈t.val,(u i:ℤ))+2-2*t.val.card≤p) : Level p (fun x=> (connected (moments R (Normal.blend Q (μ x)) w)).part t) :=
    drawn Q μ hμ t u w p t.val (Subset.refl _) hw (fun _ he hh=>False.elim (hh he)) h
end YM.Comparison.RG02.Valence
