import YM.FormalOPE.RG10.Position.Discrete
import YM.FormalOPE.RG10.Position.Fields

/-!
# Across horizons and H; normalization of the common *adjusted* prescription
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Position.Grade
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle Matrix
open scoped Topology BigOperators ContDiff Classical
variable {J K : Type*} [Fintype J] [DecidableEq J] {w:J→ℕ}
  [Fintype K] [DecidableEq K] {v:K→ℕ} (f:K↪J) (xJ:∀ i, w (f i)=v i) (hx:∀ i j,v i ≥ w j → j ∈ Set.range f)
variable {g:Flow} (h:Passe g w) (k:Passe g v)

section
include xJ
omit [Fintype J][Fintype K][DecidableEq J][DecidableEq K] in
lemma across {L:Matrix J J fps} (hl : Cut w L) : Cut v (L.submatrix f f):= fun i j hi=> hl (f i) (f j) (by rw [xJ,xJ]; exact hi)
omit [Fintype J][Fintype K][DecidableEq J][DecidableEq K] in
lemma tile_across (L:Matrix J J fps) : tile v (L.submatrix f f) = (tile w L).submatrix f f := by ext i j : 1; simp [tile,xJ]
include hx
omit [DecidableEq K] in
lemma crossed {L:Matrix J J fps} (T:Matrix J J fps)(hl:Cut w L) : (L*T).submatrix f f = L.submatrix f f * T.submatrix f f := by
 ext i j : 1; rw [Matrix.submatrix_apply, Matrix.mul_apply,Matrix.mul_apply]
 let A (k:J) := L (f i) k * T k (f j)
 change ∑ k,A k=∑ k,A (f k)
 conv_rhs => rw [← sum_image (f:=A) (by exact f.injective.injOn)]
 symm; apply sum_subset (subset_univ _); intro k _ hu; have ht : v i < w k := by
   by_contra! hh; obtain ⟨u,he⟩:= hx i k hh; exact hu (mem_image.mpr ⟨u,mem_univ _,he⟩)
 unfold A; rw [hl (f i) k (by rw [xJ]; exact ht), zero_mul]
lemma book_across (hv : ∀ s,(h.train s).submatrix f f=k.train s) : h.book.submatrix f f=k.book := by
 refine k.recovered (across f xJ h.booked.1) ?_ ?_
 · rw [tile_across _ xJ,h.booked.2.1]; exact submatrix_one_embedding ..
 unfold Passe.demand Retry.inter; apply sub_eq_zero.mpr
 have hs := congr_arg (fun u:Matrix J J fps=> u.submatrix f f) h.first_step;
 rw [crossed f xJ hx _ (h.booked.1.carries (g.warp 1)), crossed f xJ hx _ (layer_cut (h.station_block _)), hv] at hs
 unfold Passe.drive at *; rw [← tile_across _ xJ,hv] at hs; exact hs
end

-- H action in the **same** Deck bases, real signed-coordinate ambient up to the limit and using
-- this cost (actual scale-specific symmetry from WilsonX regulator limits is an input).
variable {G:Gauge}{F:Frames G}
def swing (d:ℕ)(s:Signed) : Matrix (Deck F d) (Deck F d) ℝ:= of fun i j=> ((deck F d).repr (ride F s.ortho d (deck F d i)) j).re
lemma swing_deck (d:ℕ)(s:Signed) (i j : Deck F d) : (↑(swing d s (F:=F) i j):ℂ)=(deck F d).repr (ride F s.ortho d (deck F d i)) j:=by
 apply Complex.conj_eq_iff_re.mp; let b:=deck F d; let x:= ride F s.ortho d (b i); let c (j:Deck F d):=star (b.repr x j)
 have hv: ∑ j,c j • b j=x:= by
   have hh:=congr_arg ((freeTable F).conj (table_spin F) d) (b.sum_repr x); simp_rw [map_sum,map_smulₛₗ] at hh; simpa only [b,x,c,starRingEnd_apply,real_move,deck_real] using hh
 have hx : b.repr (∑ j,c j • b j) j=c j:= by rw [map_sum,Finsupp.finsetSum_apply]; simp [Finsupp.single_apply]
 rw [hv] at hx; exact hx.symm
lemma swing_grade (d:ℕ)(s:Signed) : Layer (Deck.price F d) (swing d s) := by
 intro i j H; unfold swing; simp only [Matrix.of_apply,grade_zero F d j (m:=Deck.grades F d i) (fun h=> H (congr_arg Prod.fst h)) (Loft.respected d s.ortho _ (grade_written F d i)), Complex.zero_re]

structure Rails (F:Frames G) where
  flow : Flow
  ok : Cycle flow
  route d : Passe flow (Deck.price F d)
  nested i j (h:i≤j) s : ((route j).train s).submatrix (Deck.climb F h) (Deck.climb F h) = (route i).train s
  unit d i j : (route d).train i (Deck.start F d) j= (1 : Matrix _ _ fps) (Deck.start F d) j
  rotation d t s : ((route d).train t) * ((swing (F:=F) d s).map C)=((swing (F:=F) d s).map C) * ((route d).train t)

namespace Rails
variable (R:Rails F) (s:Signed) (t:ℝ)(d:ℕ)
abbrev book (j:ℕ) := (R.route j).book
abbrev drive := (R.route d).drive t
lemma scaled_across {d e:ℕ}(h:d ≤ e) : (R.book e).submatrix (Deck.climb F h) (Deck.climb F h) = R.book d:= by
 let f: Deck F d ↪ Deck F e := ⟨_,Deck.climb_inj F h⟩
 exact book_across f (fun i=>rfl) (fun i j h'=>Deck.of_price F h (le_trans h' (Deck.price_bound F d i))) (R.route e) (R.route d) (R.nested d e h)
lemma leaves_unit (i : Deck F d) : R.book d (Deck.start F d) i = (1:Matrix _ _ fps) (Deck.start F d) i:= by
 by_cases hh: Deck.price F d i=0
 · have he:= congr_fun₂ (R.route d).booked.2.1 (Deck.start F d) i; rw [tile,Matrix.of_apply,if_pos (by exact hh.symm)] at he; exact he
 have he : (i ≠ Deck.start F d) := fun h=>by subst i; exact hh rfl
 rw [Matrix.one_apply_ne he.symm]; exact (R.route d).booked.1 _ _ (show (0:ℕ) < _ from Nat.pos_of_ne_zero hh)
lemma preserves : R.book d * ((swing (F:=F) d s).map C)=((swing (F:=F) d s).map C) * R.book d:= by
 symm; refine Passe.commute_w _ _ (R.rotation d 1 s).symm ?_ ?_
 · ext i j : 1; simp only [Matrix.map_apply, Flow.at_const]
 intro i j h; rw [map_apply, swing_grade d s _ _ h,map_zero]

end Rails
end YM.FormalOPE.RG10.Position.Grade
