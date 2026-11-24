import YM.OPE.Compatible.Bust.Toast
/-!
# restrict Seat. momentWard and Cold.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Float
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra RG Work.F08 Matrix
open scoped Topology BigOperators Classical
open Cascade Terp Paver Rill Shell FreeResolvent Exterior MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
variable {I K E F X:Type}{m r i j n k:ℕ}{C D:ℝ}{N:Side}{v:Train r}{G:Gauge} {L:KernelChoices}
-- Closed regular
noncomputable def bed (G:Gauge)(k m:ℕ): Submodule ℝ (Seat k m (Shade G)) where
     carrier:=setOf fun p=>∀ i:ℕ,lilies m k _ p i∈ cope G i m
     zero_mem':=fun i=>by rw [map_zero]; exact Submodule.zero_mem _
     add_mem':=fun {p q} (h:∀i,_) (hp:∀i,_) i=>by rw [map_add,Pi.add_apply]; exact (cope G i m).add_mem (h i) (hp i)
     smul_mem':=fun r x (h:∀i,_) i=>by rw [map_smul, Pi.smul_apply]; exact (cope G i m).smul_mem _ (h i)
lemma merit {p:Seat k m (Shade G)}(hp:p∈ bed G k m) (i:ℕ):
      let q:= lilies m k _ p i
      q.abides ∧ q.sorted∧ q.painted:=by
          intro q; obtain ⟨_,hh,ha,h⟩:= (patent (⟨q,hp i⟩:cope G i m)); exact ⟨hh,h,ha⟩
lemma pell {p:Seat k m (Shade G)}(hp:p∈ bed G k m)(x:Site N): formSong m k G x p∈harmon (Vec G N 1) k:=by
      let q:= lilies m k _ p; let f:= formSong m k G x p; have he(i:ℕ):Summable (q i):= tiller m _; refine ⟨?_,?_⟩
      · intro i hi; have ht:q i=0:= (sproutV m k p).1 i hi; ext1 y; unfold q at ht; rw [tensors, ht]; simp [scribe]
      intro i u v; simp_rw [tensors]; rw [show deckW G N ∘ u ∘ v= (deckW G N∘u)∘ v from rfl,← rotating v, show swing _ _= _ from (merit hp i).2.1 v]
-- Lap(same) finite oath carries on own phase
lemma sax {p:Seat k (m+1) (Shade G)}(hp:p∈bed G k (m+1))(v: Train r)(h:4 ≤ r)(q:ℕ)(x:Site N):
     let A:= Prog L v G N
     let V:= pointAt G v h L N; let M:=lapD V (m+1) k p; let R:= formSong (m+1) k G x M q; Tensor.Sym R∧ Reserve A R:=by
         intro A V M R; let D:= formSong (m+1) k G x p; let T:= PhV L v G N; have he:R=opus T D q:=formulaS p v h x q; rw [he]; refine ⟨?_,OpusCoef D (fun i=>reserves p v h _ x (merit hp i).1) _⟩; have hv:= (show reduces (harmon (Vec G N 1)) (opus T) from (by simpa only [one_smul] using opusReducer T 1)); exact ((show opus T D∈ harmon _ (k-1) from (hv k _ (pell hp x)).2).2) q
lemma lip {p:Seat k m (Shade G)}(hp:p∈ bed G k m)(v:G.El)(q:ℕ)(n:Side):
      let T:=formSong m k G (0:Site n) p
      pulling (magicL G n v) T q = T q :=by
           intro T; ext1 x; change T q (fun i=> (magicL G n v)*ᵥ x i)=T q x; unfold T; simp_rw [magicB,tensors]; let d(i):= deckW G n (x i); rw [show deckW G n ∘ (fun i=>chipHue v (x i)) = (fun i=> hue v (d i)) from funext fun i=> (deckW G n).apply_symm_apply _]; exact (merit hp q).2.2 n _ v
lemma repel {p:Seat k m (Shade G)}(hp:p∈ bed G k m)(v:G.El)(u:Train r)(hh:4 ≤ r)(q:ℕ)(n:Side):
      let T:=formSong m k G (0:Site n) (lapD (pointAt G u hh L n) m k p)
      pulling (magicL G n v) T q=T q:=by
          intro T; let x:=formSong m k G (0:Site n) p; rw [show T=opus (PhV L u G n) x from funext fun i=> formulaS p u hh _ i]; exact arcing x q v u L (lip hp v _ _)
end YM.OPE.Silt.Float
