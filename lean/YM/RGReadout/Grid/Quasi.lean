import YM.UVExt.ActualTie
import YM.RGReadout.Grid.Observation
import YM.OPE.Samples.Layout

/-!
# Reading the unselected data at any non-coincident points

Consume UVExt.ActualTie on the same Base from Services. Important
specialism: arbitrary axis overlaps allowed OFF diagonals. Integrals
normalize with the actual Wilson law.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGReadout.Literal
open Finset Function Filter Set MeasureTheory Analysis Wilson Lattice RG Source Extra.Histories
open MergeProof MergeProof.Accent MergeProof.Ribbons Trace.Physical Trace.Physical.GermGraph
open Overlay Work.G08 Bid Next.Rank Next.UVStress Price OPE
open Extraction Spec Cells OPE.Cards
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {G : Gauge} {C : Family G} {F : Extraction.Order} {S : Table C.book}
variable (U : Spec.Final C F S) {m k n : ℕ} (hs : Services C F S)
include hs

lemma cornerLimit (p : Fin n → C.book.Token) (K : Set (Points n)) (ht : IsCompact K) (he : K ⊆ conf _) :
    ∀ ε : ℝ, 0<ε → F.late fun N b=> ∀ v : Fin n → Cover, tag (C.S.a N) v ∈ K →
      dist (Extraction.lifted C N b p v) (S.read (tag (C.S.a N) v) p) < ε := by
  obtain ⟨a,B,c,L,h⟩ := hs.along
  let hU := UVExt.interim h
  intro ε hε
  filter_upwards [hU.tied n K ht he p, (hU.tiles n p).uniform K he ht (ε/2) (by positivity)] with i hi hV
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hi.2 (ε/2) (by positivity)] with j hj v hv
  let t:= tag (C.S.a (F.mesh j)) v
  let M:= S.read t p
  let I:= UVExt.Grid.picture C F (F.per i) n p
  let X:= UVExt.Grid.film C p (F.mesh j) (F.per i)
  have hM : X t = Extraction.lifted C (F.mesh j) (F.per i) p v :=
    UVExt.Grid.at_tag (C.S.a_pos _) v _
  rw [← hM]; change dist (X t) M < _
  refine (dist_triangle _ (I t) M).trans_lt (lt_of_lt_of_le (add_lt_add (b:=ε/2) ?_ (hV _ hv)) ?_)
  · rw [dist_comm]; exact hj _ hv
  linarith

/-- Use ordinary braid on Any injection. Uses exact moment limits at axis
    ties from InterimTie on Base; not available via Seed.generic alone. -/
lemma variationAt {d:Caps n} (b : Fin n→ Cover) (hb : Extraction.Order.grid C k b ∈ conf _)
    {l:Filter (ℕ×ℕ)} (p : C.book.Vector d)(w : ℕ×ℕ → C.book.Vector d)
    (hp:∀ i,Tendsto (fun v=> w v i) l (𝓝 (p i))) (ht:l ≤ F.fuse) : Tendsto
      (fun i:ℕ×ℕ => C.ensemble d (fun j => location C.S k i.1 i.2 (b j)) (w i)) l
      (𝓝 (S.value d (Extraction.Order.grid C k b) p)):=by
  let E (i) := dial (L:= C.book) d i
  let J := (i:Fin n)→ (C.book.coord (d i)).Index; letI : Fintype J:= Pi.instFintype
  let Y (r:J) i:= E i (r i); let W(F:C.book.Vector d)(r:J):= ∏ i,(E i).repr (F i) (r i)
  have he(X:Moment C.book n d)(t:C.book.Vector d): X t=∑ j:J,W t j*X (Y j):=by
    have hx:t= fun i=> ∑ k,(E i).repr (t i) k • E i k:= funext fun i=> ((E i).sum_repr _).symm
    conv_lhs=> rw [hx]
    rw [MultilinearMap.map_sum]; exact Finset.sum_congr rfl (fun j _=> X.map_smul_univ (fun k=>(E k).repr (t k) (j k)) _)
  let X:= Order.grid C k b
  have hS(t:J): Tendsto (fun i:ℕ×ℕ=> C.ensemble d (fun j=> location C.S k i.1 i.2 (b j)) (Y t)) l
    (𝓝 (S.value d X (Y t))) := by
    refine Metric.tendsto_nhds.mpr fun ε hε=>?_
    let v (i:Fin n) : C.book.Token := ⟨d i,Y t i⟩
    have he := cornerLimit hs v {X} isCompact_singleton (singleton_subset_iff.mpr hb) ε hε
    have he : ∀ᶠ i in F.fuse, ∀ z : Fin n → Cover, tag (C.S.a i.1) z ∈ ({X}:Set (Points n)) → dist (Extraction.lifted C i.1 i.2 v z) (S.read (tag (C.S.a i.1) z) v) < ε := he
    filter_upwards [(Cards.largeMesh F|>.mono_left ht).eventually_ge_atTop k,
      he.filter_mono ht] with i hk hi
    let z u := zoom C.S (show k ≤ i.1 from hk) (b u)
    have hx : tag (C.S.a i.1) z=X := by
      ext1 j; exact zoom_grid hk _
    have ht := hi z (mem_singleton_iff.mpr hx)
    change dist (C.numeric i.fst i.snd v _) (S.read _ v) < ε at ht
    rw [hx, show wrap _ ∘ z=(fun j=>location C.S k i.1 i.2 (b j)) from ?_] at ht
    · exact ht
    exact funext fun j=> by unfold Cells.location; rw [dif_pos (show k ≤ i.1 from hk)]; exact (Log.Trunk.Canvas.neighbor (b j) hk).symm
  have hW(t:J):Tendsto (fun i:ℕ×ℕ => W (w i) t) l (𝓝 (W p t)):=
    tendsto_finsetProd _ (fun k _=> ((E k).coord (t k)).continuous_of_finiteDimensional.continuousAt.tendsto.comp (hp k))
  rw [he (S.value ..)]; exact (tendsto_finsetSum Finset.univ (fun i _=> (hW i).mul (hS i))).congr'
    (Eventually.of_forall fun i=> (he (C.ensemble d (fun j=> location C.S k i.1 i.2 (b j))) (w i)).symm)

set_option quotPrecheck false
local notation "q'" => C.S.gridPoint k
section
variable {I : Type} [Fintype I] {J : I → ℕ} {p : I → Cover}
    (w : ∀ i:I, C.label (J i))

def literalAt (C : Family G) {J:I→ℕ} (k : ℕ) (p : I → Cover)
    (u : ∀ i:I, ℕ × ℕ → C.label (J i)) (N b : ℕ) (x : Config G (C.side N b)) : ℂ :=
  ∏ i, C.O N b (u i (N,b)) (location C.S k N b (p i)) x
omit hs in
lemma through_fields {I:Type}[Fintype I] {d:I→ℕ} {p:I→E4}
    (w : ∀ i,C.label (d i)) (h: Injective p)
    {T : Table C.book} (hT:T.Hierarchy) (hS:T.respects S) :
    observe T p (fun i:I=>Sigma.mk (d i) (w i)) = Orbits.moment T p (fun i=> S.project _ (w i)) := by
  rw [Orbits.observed,observe_exact (S:=S) T _ hT.laws.toSymmetric hS h,
    observe_exact (S:=S) T _ hT.laws.toSymmetric hS h]
  apply congr_arg (S.useAt T _)
  funext i; unfold Orbits.names; change (⟨_,S.project _ _⟩:S.Tag)=(⟨_,S.project _ _⟩:S.Tag);
  erw [S.rep]
include U
lemma close_to_hierarchy {l:Filter (ℕ×ℕ)} (hp:l ≤ F.fuse) (u : ∀ i,ℕ × ℕ → C.label (J i))
    (hx : Injective (q' ∘ p)) (hw : ∀ i, Tendsto (u i) l (𝓝 (w i))) :
    Tendsto (fun i : ℕ×ℕ => C.omega i.1 i.2 (literalAt C k p u i.1 i.2)) l
      (𝓝 (Orbits.moment S (q' ∘ p) (fun i=> S.project _ (w i)))) := by
  rw [← through_fields w hx U.room.kernel (fun _ => le_rfl),observe,worded,S.readAt]
  apply Tendsto.congr' _ (variationAt hs (p ∘ runNames I) (runs_conf.mpr hx) (d:=J ∘ runNames I)
    (fun i=> w (runNames I i)) (fun j i=>u (runNames I i) j) (fun i=>hw (runNames I i)) hp)
  refine Eventually.of_forall ?_
  rintro ⟨N,b⟩
  refine congr_arg (C.omega N b) ?_
  funext U
  exact Equiv.prod_comp (runNames I) (fun i=> C.O N b (u i (N,b)) (location C.S k N b (p i)) U)
end
end YM.RGReadout.Literal
