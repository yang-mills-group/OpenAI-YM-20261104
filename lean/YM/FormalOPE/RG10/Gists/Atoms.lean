import YM.Next.MULTISOURCE.Shards
import YM.FormalOPE.RG10.Rupture.Finance
/-! # Projective connected-legend in any polynomial PS, by pointwise evaluation
 on scalar census with coupling, BEFORE calibration. Primitive log and ordinary families
 interconvert at distinct-mark root layout, entries typed as all Hot(R) positions with
 upward completion (width finite for all operations). Next investment on tuples.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Gists
open Function PowerSeries Marker Finset Word
open Multi (parts substitute shards Hot unionOf)
open scoped Topology BigOperators Classical
variable {I : Type} [Fintype I] [DecidableEq I]
variable (R:Census I)

namespace Word
variable {R} (f:Word (parts R)) (x:R.Mode)
/-- preserve same coefficient binding. enumerate partitions only of slots. -/
def parcel (R:Census I): Word (parts R)→+* Word R:= PowerSeries.map (substitute R)
omit [Fintype I] in
lemma parcels (x:R.Mode): see x (parcel R f) = ∑ i∈ shards R x,see i f:= by apply PowerSeries.ext; intro n; rw [map_sum,unfold_see,parcel,coeff_map]; simp_rw [unfold_see]; exact Multi.substituted ..
omit [Fintype I] in
@[simp] lemma pacify : Word.vac R (parcel R f)=Word.vac (parts R) f:= by rw [Word.vac_eq, Word.vac_eq,parcels,Multi.shards_quiet, Finset.sum_singleton]
omit [Fintype I] in
lemma pie (x:ℂ) : parcel R (x • f) = x • parcel R f:= by apply PowerSeries.ext; intro i; simp [parcel,PowerSeries.coeff_map] -- inspect
abbrev until' (p:Word R)(r:ℕ) := ∑ t∈ range (r+1), (↑t.factorial:ℂ)⁻¹ • p^t
lemma expands (p:Word R)(he:vac R p=0)(i:ℕ)(ht:Fintype.card I ≤ i): expMark p=until' p i:=by apply sum_subset (range_mono (by omega)); intro j hj hi; rw [marker_nil he (show Fintype.card I<j by simp only [mem_range] at hi; omega), smul_zero]
lemma expense (h:vac (parts R) f=0): parcel R (expMark f)=expMark (parcel R f):= by
 let i:=max (Fintype.card I) (Fintype.card (Hot R)); rw [expands f h i (le_max_right ..), expands (R:=R) _ (by rw [pacify]; exact h) i (le_max_left ..)]; unfold until'; simp_rw [map_sum,pie,map_pow]
lemma packup (h:vac (parts R) f=1): parcel R (logWord f)=logWord (parcel R f):= by
 have hx:vac R (parcel R (logWord f))=0:= by rw [pacify,vac_log _ h];
 rw [←log_exp _ hx,←expense _ (vac_log _ h), exp_log _ h]
omit [Fintype I] in
lemma pitch (s : (parts R).Mode)(f:Series): parcel R (sing s f)=sing (unionOf s) f:= by
 apply PowerSeries.ext; intro i; unfold parcel; rw [coeff_map];
 have hv {I : Type} [DecidableEq I](R:Census I)(s:R.Mode): coeff i (sing s f)=Poly.send s (coeff i f):=by ext t; rw [←unfold_see]; by_cases hx:t=s <;> simp [hx]
 simp_rw [hv]; exact Multi.substituteL_send ..

variable (x:Hot R) (p:Series)
omit [Fintype I] in
lemma hot (x: Hot R): (x.val : R.Mode) ≠ R.quiet:= fun he=> Finset.nonempty_iff_ne_empty.mp x.property (congr_arg Subtype.val he)
omit [Fintype I] in
@[simp] lemma hot_off : vac R (sing x.val p)=0:= by rw [vac_eq,see_sing,if_neg (hot x).symm]
omit [Fintype I] in
lemma square : (sing x.val p)^2=0:= by
 apply observe_ext; intro s; rw [pow_two,convolves]; simp_rw [see_sing]; rw [see_zero]; apply sum_eq_zero; intro i _; apply sum_eq_zero;intro j _
 split_ifs with h hi hj; all_goals (first | (solve | simp) | (exfalso; obtain ⟨z,hz⟩:= x.property; exact disjoint_left.mp h.1 (hi.symm ▸ hz) (hj.symm ▸ hz)))

@[simp] lemma launched : expMark (sing x.val p)=1+sing x.val p:= by
 rw [expands _ (hot_off x p) (Fintype.card I+1) (by omega),until',Finset.sum_range_succ', Finset.sum_range_succ']; have hz (i:ℕ): sing x.val p^(i+1+1)=0:= by rw [show i+1+1=i+2 from rfl, pow_add,square,mul_zero]
 simp_rw [hz]; simp [add_comm]
end Word
end YM.FormalOPE.RG10.Gists
