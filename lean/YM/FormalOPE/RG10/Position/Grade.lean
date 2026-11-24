import YM.FormalOPE.RG10.Position.Mint

/-!
# Mass-independent WilsonX adjustment via a discrete normal form

See `consequences`. No expansion assuming power series convergence. To solve for the finite
counter-rotations it's enough to use one nontrivial dilatation (e.g. e), no need smooth generator
arguments, because triangular off-grade resonance is impossible. All statements formal. Uses same
unit label horizon as in Deck. Coarse matrix indexing Row input j, emitted fine-to-that-counterpart
mode k (column acts on right). -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Position.Grade
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle Matrix
open scoped Topology BigOperators ContDiff Classical
variable {J K : Type*}
section ring
variable (g:J→ℕ){S R:Type*}[CommRing S][CommRing R]
variable {L M : Matrix J J S}
def Cut (T: Matrix J J S) := ∀ i j, g i < g j→ T i j=0
def Trim (T: Matrix J J S) := ∀ i j, g i ≤ g j→T i j=0
def Layer (T: Matrix J J S) := ∀ i j, g i ≠ g j→ T i j=0
def tile (T: Matrix J J S) : Matrix J J S := of fun i j=> if g i=g j then T i j else 0
variable [Fintype J] [DecidableEq J] {g}
omit [Fintype J] [DecidableEq J] in
lemma tile_layer : Layer g (tile g M) := fun _ _ h=> if_neg h
omit [Fintype J] [DecidableEq J] in
lemma layer_fixed (hu :Layer g M) : tile g M=M:=Matrix.ext fun i j=> by
  by_cases h:g i=g j
  · unfold tile; simp [h]
  unfold tile; rw [of_apply,if_neg h]; exact (hu i j h).symm
omit [Fintype J] [DecidableEq J] in
lemma layer_cut (hu:Layer g M): Cut g M:=fun i j h=>hu i j h.ne
omit [Fintype J] [DecidableEq J] in
lemma trim_cut (ht:Trim g M): Cut g M:=fun i j h=>ht i j h.le
omit [Fintype J] [DecidableEq J] in
lemma Cut.add (hu:Cut g L)(ht:Cut g M):Cut g (L+M):=fun i j h=> by rw [Matrix.add_apply,hu i j h,ht i j h,add_zero]
omit [Fintype J] [DecidableEq J] in
lemma Cut.sub (hu:Cut g L)(ht:Cut g M):Cut g (L-M):=fun i j h=> by rw [Matrix.sub_apply,hu i j h,ht i j h,sub_zero]
omit [DecidableEq J] in
lemma Cut.mul (hu: Cut g L) (ht: Cut g M): Cut g (L*M) := by
  intro i j h; rw [Matrix.mul_apply]; apply sum_eq_zero; intro k _; by_cases h':g i<g k
  · rw [hu i k h',zero_mul]
  rw [ht k j (lt_of_le_of_lt (le_of_not_gt h') h),mul_zero]
omit [DecidableEq J] in
lemma Cut.tile (hu:Cut g L)(ht:Cut g M): Grade.tile g (L*M)= Grade.tile g L * Grade.tile g M:= by
  ext i j; by_cases h:g i=g j
  · unfold Grade.tile; rw [Matrix.of_apply,if_pos h, Matrix.mul_apply,Matrix.mul_apply]; apply sum_congr rfl; intro k _; simp only [Matrix.of_apply]; rcases lt_trichotomy (g i) (g k) with h'|h'|h'
    · simp [h'.ne,hu i k h']
    · simp only [h', ← h, if_true]
    simp [h'.ne',ht k j (h ▸ h')]
  rw [tile_layer i j h]; rw [Matrix.mul_apply]; symm; apply sum_eq_zero; intro k _; by_cases h':g i=g k
  · rw [tile_layer k j (by omega),mul_zero]
  rw [tile_layer i k h',zero_mul]
omit [Fintype J] [DecidableEq J] in
lemma tile_add : tile g (L+M)=tile g L+tile g M:= by ext i j; by_cases h:g i=g j <;>simp [tile,h]
omit [Fintype J] [DecidableEq J] in
lemma tile_sub : tile g (L-M)=tile g L-tile g M:= by ext i j; by_cases h:g i=g j <;>simp [tile,h]
omit [Fintype J] [DecidableEq J] in
lemma zero_tile (ht:Trim g L): tile g L=0:=by
  ext i j; by_cases h:g i=g j 
  · simp [tile,h, ht i j h.le]
  simp [tile,h]
omit [Fintype J] [DecidableEq J] in
lemma Cut.crush (ht:Cut g L)(h:Grade.tile g L=0):Trim g L:=fun i j hu=> (hu.lt_or_eq.elim (fun hx=>ht i j hx) (fun hx=>by
  rw [← show Grade.tile g L i j=_ from if_pos hx, h, Matrix.zero_apply]))
omit [Fintype J] in
lemma tiled_one (g:J→ℕ) : Layer g (1 : Matrix J J S):= fun i j h=> by rw [Matrix.one_apply_ne (fun w=> by subst j; contradiction)]
omit [Fintype J] [DecidableEq J] in
lemma tile_map (f : S →+* R) : tile g (M.map f)=(tile g M).map f:=by ext i j; by_cases h:g i=g j <;>simp [tile,h]
omit [Fintype J] [DecidableEq J] in
lemma Cut.carries (f:S→+* R)(ht:Cut g M): Cut g (M.map f):= fun i j h=> by simp [ht i j h]
-- keep finite projective restriction proof
end ring
end YM.FormalOPE.RG10.Position.Grade
