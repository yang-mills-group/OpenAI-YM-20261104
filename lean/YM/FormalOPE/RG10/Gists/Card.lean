import YM.FormalOPE.RG10.Gists.Plot
/-!
 # Algebraic log recurrence on set-of-slots choices. Compatible at all finite grades. Nobody
 changes width at one coupling prefix to emulate the answers. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Gists.Card
open Function PowerSeries Finset Route Gists.Word RG10.Word Marker Primitives.GCC
open Multi (parts substitute shards Hot unionOf)
open scoped Topology BigOperators Classical
variable {I X:Type} [Fintype I] [DecidableEq I]
variable (R:Census I) (f:R.Mode→Channel X)(g: Hot R→Channel X)
local notation "T"=> R.Mode
local notation "Π'"=> Anchor.diff

def cover (f:R.Mode→Channel X) (k:R.Mode) (v:I) (q:R.Mode→Channel X): Channel X:= f k - ∑ t ∈ ((univ (α:=R.Mode)).erase k).filter (fun t=> t.val ⊆ k.val ∧ v∈t.val), q t * f (Anchor.diff k t.val)
-- Type (Hot) chosen by selecting one leader if available
def reveal : ℕ→ R.Mode→Channel X
| 0,_=>0
| i+1,s=> if h:s.val.Nonempty then cover R f s (Classical.choose h) (reveal i) else 0
-- recursion completed at depth=card
abbrev logRow (f:R.Mode→Channel X)(s:R.Mode):= reveal R f s.val.card s
variable (y:X→ℂ) (x:R.Mode)
omit [Fintype I] in
lemma revealed (y:X→ℂ)(H:f R.quiet=1): (RG10.Word.vac R) (seeOrd R f y)=1:= by rw [RG10.Word.vac_eq,seen,H,map_one]
namespace Budget
-- root-subtraction reversed for optics.
variable {R} (B:Word R) (h:(vac R) B=1)
include h
lemma reversed (s:R.Mode)(i:I)(hi:i∈s.val) : see s (logWord B)=see s B - ∑ t∈ (Finset.univ (α:=R.Mode)).erase s with t.val ⊆ s.val ∧ i∈t.val, see t (logWord B)*see (Anchor.diff s t.val) B:= by
 have he:boot B=1:= by rw [boot, h]; simp
 apply eq_sub_of_add_eq; rw [assembled he s hi,sum_filter,← add_sum_erase _ _ (mem_univ s)] -- may rewrite whole
 rw [if_pos (show s.val ⊆ s.val ∧ i∈s.val from ⟨Subset.rfl,hi⟩),show Anchor.diff s s.val=R.quiet from Subtype.ext (by simp [Anchor.diff,Census.quiet]),←vac_eq,h,mul_one]
end Budget

variable (H:f R.quiet=1)
include H
local notation "△"=> RG10.Word.logWord (seeOrd R f y)
lemma solid (i:ℕ)(hi:x.val.card ≤ i): run y (reveal R f i x)=see x (RG10.Word.logWord (seeOrd R f y)):= by
 induction i generalizing x with
 | zero=>
    have hx:x=R.quiet:= Subtype.ext (Finset.card_eq_zero.mp (by omega)); rw [hx, reveal, map_zero,←RG10.Word.vac_eq,vac_log _ (revealed R f y H)]
 | succ i ih=>
    obtain he|he:= eq_empty_or_nonempty x.val
    · rw [reveal, dif_neg (show ¬ x.val.Nonempty by simp [he]),map_zero, show x= R.quiet from Subtype.ext he,←RG10.Word.vac_eq,vac_log _ (revealed R f y H)]
    rw [reveal,dif_pos he, Budget.reversed _ (revealed R f y H) x _ (Classical.choose_spec he), cover,seen,_root_.map_sub,map_sum]; congr 1; apply sum_congr rfl; intro t ht
    have hv := mem_filter.mp ht; have hu:t.val.card<x.val.card:= card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hv.2.1,fun h'=> (ne_of_mem_erase hv.1) (Subtype.ext h')⟩) -- inspect
    rw [_root_.map_mul, ih _ (by omega),seen]
lemma reading : run y (logRow R f x)=see x (RG10.Word.logWord (seeOrd R f y)):= solid R f y x H _ le_rfl
lemma formula (i:I)(hi:i∈x.val) : logRow R f x=f x -∑ t ∈ ((univ (α:=R.Mode)).erase x).filter (fun t=> t.val ⊆ x.val ∧ i∈t.val), logRow R f t * f (Anchor.diff x t.val):= by
 apply runs_determine; intro y; rw [reading R f y x H, Budget.reversed _ (revealed R f y H) x i hi,seen,_root_.map_sub,_root_.map_sum]; simp_rw [_root_.map_mul, reading R f y _ H,seen]
omit H [Fintype I] in
@[simp] lemma off : logRow R f R.quiet=0:= rfl
lemma foremost : dramatize R (fun x: Multi.Hot R=>logRow R f x.val) y= RG10.Word.logWord (seeOrd R f y):= by
 apply observe_ext; intro s; obtain hh|hh:= eq_empty_or_nonempty s.val
 · rw [show s=R.quiet from Subtype.ext hh,←RG10.Word.vac_eq,←RG10.Word.vac_eq,under,vac_log _ (revealed R f y H)]
 let z : Hot R:=⟨_,hh⟩; exact (sees R (fun x: Multi.Hot R=>logRow R f x.val) y z).trans (reading R f y s H)
lemma moment_law : program R (fun x: Hot R=> logRow R f x.val) x=f x:= by
 apply runs_determine; intro y; rw [← seen,← plotting, foremost R f y H, exp_log _ (revealed R f y H),seen]
omit H
@[simp] lemma genuine (x:Multi.Hot R) : logRow R (program R g) x.val=g x:= by
 apply runs_determine; intro y; rw [reading R _ y _ (blank ..),← plotting,log_exp _ (under ..),sees]
end YM.FormalOPE.RG10.Gists.Card
