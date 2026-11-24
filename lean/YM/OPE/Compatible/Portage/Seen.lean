import YM.OPE.Compatible.Glades.Process
/-! Native span. Units clock ruler on finest dyadic grid sitting in the rotated torus. Lifts respect shifts. All results are torus, except explicit period extension (fixed UV!). -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Pixel
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float Next.Rank Station Next.Rank.Spindle
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi Finset Cells Ribbon
open scoped Topology Classical
variable {G:Gauge}(C:Family G){n p i j J:ℕ}
-- order of est in n
def width (C: Family G)(i p:ℕ)(x y:Site (C.side i p)) := C.S.a i * (separation x y:ℝ)
variable (p)
lemma width_triangle {i:ℕ}(x y z: Site (C.side i p)) : width C i p x z ≤ width C i p x y+width C i p y z :=by
   unfold width; rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast separation_triangle x y z) (C.S.a_pos _).le
lemma width_comm {i:ℕ}(x y: Site (C.side i p)) : width C i p x y=width C i p y x:=by unfold width; rw [separation_comm]
lemma width_move (i:ℕ) (s:Signed)(v x y: Site (C.side i p)) : width C i p (affine s v x) (affine s v y)=width C i p x y:=by simp [width,affine] -- names
lemma embed_width (h:i ≤ j) (x y: Site (C.side i p)) :
    width C j p ((C.S.toDepth h p).embed x) ((C.S.toDepth h p).embed y) = width C i p x y := by
   unfold width; rw [Station.both,Nat.cast_mul, ← mul_assoc,C.S.embeds_scale]
lemma centered_width (h:i ≤ j)(x:Site (C.side j p)): width C j p x ((C.S.toDepth h p).embed ((C.S.toDepth h p).parent x)) ≤ C.S.a i :=by
   let T:= C.S.toDepth h p
   refine le_trans (?_ : _≤ C.S.a j * T.count.val) (C.S.embeds_scale T).le; refine mul_le_mul_of_nonneg_left ?_ (C.S.a_pos j).le
   have ht:= (midway T (C.S.toDepth_odd h p) x); apply Nat.cast_le.mpr; change separation x (T.embed (T.parent x)) ≤ T.count.val; omega
lemma cellShift (h:i ≤ j) (x y: Site (C.side j p)):
    |width C j p x y-width C i p ((C.S.toDepth h p).parent x) ((C.S.toDepth h p).parent y)|≤ 2*C.S.a i:=by
   rw [← embed_width C p h,abs_le]; let r:= C.S.toDepth h p; let a:= r.embed (r.parent x); let b:=r.embed (r.parent y); change _ ≤ width C j p x y-width C j p a b ∧ width C j p x y-width C j p a b≤ _
   have hx:=centered_width C p h x; have hy:=centered_width C p h y; change width C j p x a≤ _ at hx; change width C j p y b≤_ at hy
   exact ⟨by linarith only [hx,hy,width_triangle C p a x b,width_triangle C p x y b,width_comm C p a x],by linarith only [hx,hy,width_triangle C p x a y,width_triangle C p a b y,width_comm C p b y]⟩
variable {p}
-- torus consistent direction
lemma grid_diff (i:ℕ)(x y:Cover) : C.S.gridPoint i x-C.S.gridPoint i y=C.S.gridPoint i (x-y):= by
   have hi:= Work.B16.grid_add (C:=C) (k:=i) (x-y) y; rw [sub_add_cancel] at hi; exact eq_sub_of_add_eq hi.symm|>.symm
lemma width_yoke (i:ℕ)(x y:Cover): ∀ᶠ p:ℕ in atTop,
    width C i p (wrap (C.side i p) x) (wrap (C.side i p) y) ≤ ‖C.S.gridPoint i x-C.S.gridPoint i y‖ ∧
    ‖C.S.gridPoint i x-C.S.gridPoint i y‖ ≤2*width C i p (wrap (C.side i p) x) (wrap (C.side i p) y):=by
   rw [grid_diff]; filter_upwards [faraway C i (x-y)] with p hp; rw [← hp]
   let V := wrap (C.side i p) (x-y); obtain ⟨hx,he⟩:= normC C i p V
   have ht:separation V 0= separation (wrap (C.side i p) x) (wrap (C.side i p) y):=by unfold separation V; rw [sub_zero,map_sub]
   unfold width; rw [← ht]; exact ⟨hx,he.trans (le_of_eq (mul_assoc ..))⟩
end YM.OPE.Arboreal.Pixel
