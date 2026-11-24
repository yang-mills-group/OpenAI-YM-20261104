import YM.Frontier6.Exact.Panes
import YM.Frontier6.Exact.Radii

/-!
# Anchor-dual theorem on arbitrary exterior compacts.

O(4) bypass + charge subpower price. Uniform in ALL receiving phases and
angular, spectator positions and coefficients. This avoids having to pass
cutoff tie estimates also on exteriors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6
open Function Filter Set Lattice Wilson RG Source Labels MergeProof MergeProof.Ribbons Next.UVStress
open Bid Spec Analysis Table Extraction.Lease Cells Extraction.Around OS Word MeasureTheory Org Canvas Platform
open Next.Extract Dash PhysicalNext.Repeat.Legato
open scoped Topology InnerProductSpace BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {S:Table C.book} {F:Extraction.Order}
variable (K:Final C F S) (s:StateIndex K) {D n:ℕ}
set_option quotPrecheck false
local notation "T"=> K.sector.turns
lemma read_move (u:Ortho)(x:E4)(y:Points n)(v:Fin n→ S.Tag)(B:S.Field D)(hx:Points.cons x y∈conf (n+1)):
    reading K s (Ortho.move u x) (Points.move u y) ((T).label u ∘ v) D ((T).act D u B)=reading K s x y v D B:=by
    rw [reads_at,reads_at,← rotates_cons]
    rw [show Fin.cons (α:=fun _=>S.Tag) _ ((T).label u ∘ v)= ((T).label u) ∘ Fin.cons (α:=fun _:Fin (n+1)=> S.Tag) ⟨D,B⟩ v from (?_)]
    · exact turn_state K s _ _ _ hx u
    · ext1 i; refine Fin.cases ?_ (fun j=>?_) i <;> rfl
lemma family_gap {I:Type*}[Finite I]{n:I→ℕ}{L:Set (Seen n)} (h:IsCompact L)(hp:∀ y∈ L,∀ i:I,Points.cons 0 (y i)∈conf _) : ∃ c:ℝ, 0 < c ∧ ∀ y∈ L,shapes c y:=by
    let f (i:I) (x: Seen n):= Points.cons 0 (x i)
    have he (i:I): Continuous (f i):=by unfold f Points.cons points; fun_prop
    choose c hc hC using fun i:I=> gap_compact (h.image (he i)) (image_subset_iff.mpr (show L ⊆ f i ⁻¹' _ from fun x hx=> hp x hx i))
    obtain ⟨B,hb,hB⟩:= ((show ∀ᶠ t:ℝ in 𝓝[>] 0, 0<t from self_mem_nhdsWithin).and (eventually_all.mpr fun i=> (show ∀ᶠ t in 𝓝[>] 0,t<c i from mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (hc i))))).exists
    exact ⟨B,hb,fun y hy i=>gap_down (hC i _ (mem_image_of_mem (f i) hy)) (hB i).le⟩
lemma gap_inside {r:ℝ}{x:E4}{y:Points n} (he:x≠0)(hy:clearC r y)(hp:‖x‖<r):
    Points.cons x (Points.cons 0 y)∈conf (n+2):=by
    refine gap_conf (a:=0) le_rfl (gap_append (gap_down hy ((norm_nonneg _).trans hp.le)) x (fun i=>Fin.cases ?_ (fun i=>?_) i))
    · exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm he))
    apply norm_pos_iff.mpr; intro hc; have ht:= sub_eq_zero.mp hc
    have hq:r< ‖y i‖:= by simpa only [Points.cons, points_apply, Fin.cons_zero,Fin.cons_succ,sub_zero] using (show _ < ‖Points.cons 0 y i.succ - Points.cons 0 y 0‖ from hy _ _ (Fin.succ_ne_zero i).symm)
    exact hp.not_ge (le_trans hq.le (by rw [← ht]; rfl))
variable {I:Type*}[Fintype I]{N:I→ℕ}(v:Tuple S N)
variable {H:Table C.book}{M:ℕ→Table C.book}{Q:Bin H}{Y:DiffPlan S} (h:Base C F H M Q S Y) (hp:PairProducer C) (hg:G.Simple) (hW:Extraction.Wcmain C)(hG:Grill C F)
include h hp hg hW hG
variable {b d:ℕ} (B:S.Field b) (P:S.Field d)
lemma anchor_dual (D:ℕ){L:Set (Seen N)} (hL:IsCompact L)(hu:∀ y∈L,∀ i:I, Points.cons 0 (y i)∈conf _) {ε A:ℝ}(hε:0<ε)(ha:0 ≤ A):
   ∀ᶠ a:ℝ in 𝓝[>] 0, ∀ (x:E4), ‖x‖=a → ∀ (y:Seen N),y∈L→ ∀ (u:I→StateIndex K)(c:I→ℂ), (∀ p,‖c p‖ ≤ A) → kills K v y u c D →
      ‖listen K B P v y u c x‖ ≤ a^((D:ℝ)-b-d-ε):=by
   obtain ⟨r,hr,hV⟩:= family_gap hL hu; let X:= ↥L
   have hf := ((C.S.shrinks.const_mul (4:ℝ)).eventually (ge_mem_nhds (by rw [mul_zero]; exact hr))) -- use ge
   obtain ⟨b',hb,hb'⟩:= ((eventually_ge_atTop (C.ref D)).and (show ∀ᶠ i in atTop,4*C.S.a i ≤ r from hf)).exists
   choose t g hx ht using fun x:X=> towards C.S b' x.val (hV _ x.property) hb'
   let U (x:X):Set (Seen N):={y:Seen N| noSeam C.S b' (g x) (revolve (t x) y)}
   obtain ⟨l,hl⟩:=hL.elim_finite_subcover U (fun i=> (open_tile ..).preimage (pave (t i))) (fun x hx' => mem_iUnion.mpr ⟨⟨x,hx'⟩,ht _⟩)
   let R:= K.sector.turns
   let V(x:X)(i:I):= R.label (t x) ∘ v i
   have he(x:X):= seam_dual K h hp hg hW hG (R.act b (t x) B) (R.act d (t x) P) (V x) hr ha (hx x) hε b' hb
   filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hr),(eventually_all_finset l).mpr (fun i _=> he i)] with a ha ha' he x h' y hy u c hc hc'
   obtain ⟨z,hz,hZ⟩:=mem_iUnion₂.mp (hl hy)
   let w:= t z; let Z:= Ortho.move w x
   have ht:= hV y hy; have hs:shapes r (revolve w y):=fun i=>clear_rotates w _ _ (ht i)
   have hE:∀ i:I,Points.cons x (Points.cons 0 (y i))∈conf _ := fun i=> gap_inside (norm_pos_iff.mp (by rw [h']; exact mem_Ioi.mp ha)) (ht i) (lt_of_le_of_lt h'.le ha')
   have hZ':‖Z‖=a:=(Ortho.move_norm w x).trans h';
   have hr': kills K (V z) (revolve w y) u c D:=by
      intro e h A; obtain ⟨a,rfl⟩:=(R.act e w).surjective A
      refine (Finset.sum_congr rfl (g:=fun i=>c i* reading K (u i) 0 (y i) (v i) e a) (fun i _=>?_)).trans (hc' e h a)
      have hh:= read_move K (u i) w 0 _ (v i) a (hu y hy i); rw [rotates_zero] at hh; exact congr_arg (c i * ·) hh -- multiplying
   refine le_trans (le_of_eq (?_)) (he z hz Z hZ' _ hs hZ u c hc hr')
   unfold listen; refine congr_arg _ (Finset.sum_congr rfl (fun i _=>?_));
   have heq:=read_move K (u i) w x (Points.cons 0 (y i)) (Fin.cons (α:=fun _=>S.Tag) ⟨b,B⟩ (v i)) P (hE i)
   rw [rotates_cons,rotates_zero] at heq
   let v':Fin (N i+1)→ S.Tag:= Fin.cons ⟨b,R.act b w B⟩ (V z i)
   rw [show R.label w ∘ _= v' from (?_: R.label w ∘ Fin.cons (α:=fun _=>S.Tag) ⟨b,B⟩ (v i)=v')] at heq -- let R vs literal
   · exact congr_arg (c i * ·) heq.symm
   ext1 i; refine Fin.cases ?_ (fun j=>?_) i <;> rfl
end YM.Frontier6
