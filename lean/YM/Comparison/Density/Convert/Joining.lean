import YM.Comparison.Density.Convert.Annotated
import YM.Comparison.Density.Convert.Vacuum
import YM.Comparison.Density.Fusing.Padding
import YM.Next.MULTISOURCE.Render

/-!
# Join short-packet and marker conversions; one merger payment
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Convert
open Fusing Fusing.Pads Mirrors Transport RG Lattice Wilson Markers Registers Testing MeasureTheory
open Function Finset Push.AbsoluteSums Marker Multi
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side}
variable {V : Type} [DecidableEq V] {R : Census V} {X : V → Type} [∀ v, NormedAddCommGroup (X v)] [∀ v, NormedSpace ℂ (X v)]

variable (B : BudgetPoint) (O : Readers V X n) (L : Start G n) (T : Menu R X G n)

def pensions (i : Address R) (x : Cross X) (U : Config G n):= Poly.send i.1.val (leaked B T i x U)

def change : Leftovers R X G n:= Pads.insertions (baseMist B L) (ann O T) (pensions B T)

-- total of OLD markers (budget known from Hatch, also on exposed
-- subtractions with rough terms untouched).
def journal (x : Cross X) (U : Config G n):= Multi.lit R fun j=> ∑' i, preMarks T x (j,i) U

variable {K : LinkTube G} {w : V→ℝ} {B O L T} {a b c d eR eF : ℝ}
variable [Fintype V]
variable (hw : ∀ i,0<w i) (h : Cleared B K L c a eF eR) (hp : Hatch B K O T d b eF eR w)

include hp
private lemma M_ne (i : Address R) : (ann O T i).Nonempty:= by
  obtain ⟨v,hv⟩:= i.1.property
  exact ⟨_,hp.shell.contiguous i v hv (O.source.listed _)⟩
private lemma M_bears (i : Address R) (x : ℂ) : Carries O.source.uses (ann O T i) (Poly.send i.1.val x):= by
  intro j v hv he; rw [Poly.part_send,if_neg (by rintro rfl; exact he (hp.shell.contiguous i v hv))]
omit hp [Fintype V] in
private lemma blank (i : Address R) (x : ℂ) : (Poly.send i.1.val x).part R.quiet=0:= by
  rw [Poly.part_send, if_neg]; intro H; have he:= i.1.property; rw [← H] at he; exact not_nonempty_empty he

lemma pensions_supplied : Extras (ann O T) (pensions B T) B O := by
  refine ⟨M_ne hp,fun i U=>?_,fun i x U=> M_bears hp i _, fun i x U=>blank i _, fun i x k U=>?_,fun i x=> ?_,fun i x U V ha hh=>?_,fun i x U hu=>?_⟩
  · have ⟨he,hh⟩:= hp.address i U; unfold pensions
    constructor <;> intro j <;> simp_rw [Poly.part_send] <;> by_cases hi:j=i.1.val 
    · subst j; simpa using he
    · simp only [if_neg hi]; exact Slotted.vacant
    · subst j; simpa using hh
    simp only [if_neg hi]; exact fun _ _ _=>rfl
  · exact congrArg (Poly.send i.1.val) ((hp.stain i x).2.2.1 k U)
  · exact (Multi.sendC i.1.val).continuous.measurable.comp (hp.stain i x).2.2.2
  · exact congrArg (Poly.send i.1.val) ((hp.stain i x).1 U V ha hh)
  rw [pensions,(hp.stain i x).2.1 U hu,Poly.send_zero]

-- reclose sums with all test costs before summing. Absolute series at any actual test.
include hw
private lemma pins (x : Cross X) (U) : Summable fun i=> pensions B T i x U:= by
  have he (i : Hot R) : Summable fun j=> pensions B T (i,j) x U:=
    (((hp.subsides hw x i U).hasSum.map (Multi.sendC i.val) (Multi.sendC i.val).continuous)).summable
  apply Summable.of_norm
  change Summable fun j : Hot R × ℕ=> ‖pensions B T j x U‖
  exact (summable_prod_of_nonneg fun j=> norm_nonneg _).mpr ⟨fun i=> (summable_norm_iff ..).mpr (he i), hasSum_fintype _|>.summable⟩

-- need transport Budget to B
omit hw hp [Fintype V] [∀ v, NormedSpace ℂ (X v)] in
lemma Budget_smaller {e f : ℝ} (hg : 0≤eR) (hw : ∀ i,0<w i) (T : Registers R X G n)
    (h : T.Budget (later B eR hg) O w e f): T.Budget B O w e f := by
  obtain ⟨a,ha,he⟩:= h.globalCosts; obtain ⟨b,hb,hf⟩:=h.bodyCosts
  exact ⟨⟨a,ha.cheaper hw hg,he⟩,b,hb.cheaper hw hg,hf⟩
lemma bills (x : Cross X) (U) (i : Hot R) : HasSum (fun j=> preMarks T x (i,j) U)
    ((bonded O T).ledger B x i U+∑' j, leaked B T (i,j) x U):= by
  have hz : Summable (fun j=> supports B (bonded O T) x (i,j) U) :=
    (Registers.dom hw hp.shell (Budget_smaller hp.extraE hw _ hp.costs) x i).summable U
  rw [show (bonded O T).ledger B x i U=∑' j, supports B (bonded O T) x (i,j) U from (?_)]
  · simp_rw [taken B O T x]; exact hz.hasSum.add (hp.subsides hw x i U).hasSum
  simp only [ledger,orderZero,bonded,tsum_zero,zero_add]
lemma entry_bill (x : Cross X) (U : Config G n) : journal T x U=(bonded O T).log B x U+
    ∑' i,(change B O L T).marked x i U := by
  have ht:= pins hw hp x U
  have he := Pads.marked_total (baseMist B L) (ann O T) x U ht.hasSum
  unfold change; rw [he.tsum_eq]; ext i; rw [Poly.part_plus,Poly.share ht]; unfold journal
  by_cases hi:i.val.Nonempty
  · let J : Hot R:= ⟨_,hi⟩
    simp_rw [← show J.val=i from rfl,Multi.part_lit,alive,(bills hw hp x U J).tsum_eq]
    congr 1; symm
    let f:=fun i=> (pensions B T i x U).part J.val
    change (∑' i,f i)=_
    have hx : Summable f:= (ht.hasSum.map (Poly.get J.val) (Poly.get J.val).continuous).summable
    rw [hx.tsum_prod, tsum_fintype, Finset.sum_eq_single J]
    · simp [f,pensions]
    · intro b _ he; have he : J.val ≠ b.val:= fun ht=> he (Subtype.ext ht.symm); simp [f, pensions,he]
    simp
  rw [show i=R.quiet from Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp hi), Multi.part_lit_quiet]; simp_rw [baseline, pensions, blank]; simp

include h
lemma costs_change : Compensated B O (change B O L T) w eF (a+b) := by
  let f:= (fun j=> (L j.1).loss) ∘ seq n
  let g (i:Address R):= Poly.send i.1.val (expense T i)
  have hh i : 0 ≤ expense T i:= (norm_nonneg _).trans (hp.taxes i 0 (fun _=>by simp) 1)
  refine Pads.compensate f g (fun i U=>Short.charge (h.staged _) _ U) (fun i=> M_bears hp i _) (fun i=> blank i _) (fun x hx i U=> ?_) h.hitE ?_ hw
  · constructor <;> intro j <;> unfold g <;> by_cases hj:j=i.1.val
    · simp only [pensions,Poly.part_send, hj,↓reduceIte]; exact hp.taxes i x hx U
    · simp [pensions,hj]
    · simp [hj]
    simp [hj]
  have he : Poly.price w ∘ g=(fun i=> Poly.toll w i.1.val*expense T i):= by funext i; simp [g,hh]
  rw [he]; exact hp.taxed
omit hw in
lemma admissible_change : Placed B O (change B O L T):= Pads.corrected ⟨h.ready,fun i=>
    ⟨_,(neighborhood_iff ..).2 (by rw [separation_self]; exact Nat.zero_le _)⟩⟩ (pensions_supplied hp)

omit hp hw [Fintype V] [∀ v, NormedAddCommGroup (X v)] [∀ v, NormedSpace ℂ (X v)] in
lemma counted (U) : (∑' i,(change B O L T).real.value i U)= ∑' i, (baseMist B L).value i U:=
    (Pads.real_total _ _ U (h.flag_series U).hasSum).tsum_eq
end YM.Comparison.Density.Convert
