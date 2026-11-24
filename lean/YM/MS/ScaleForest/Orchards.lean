import YM.MS.ScaleForest.Sow
import YM.MS.ScaleForest.AllHistories
/-!
# The graph sum at placed inputs, divided by sectors

Every fully named calculation uses the same dimensional and subtraction
book, in the recursion here any particular height tag script at its vertices.
Homogeneous physical tags in files / subsequent changes of basis will use
this vanilla calculation. Fix a finite set of labels (`Finset W`) with
linear order establishing the anchoring convention. Last edge decomposes the
connected coefficient into two halves or a loop. If two, one side is an
unmarked root xor both sides have pins. Group histories with one/two sides
pinned accordingly. For two nonempty pin sets here we always assign the side
WITHOUT the root to be the first set, taking all order splits including zero
on either. The bulk case is different: only use lower orders with the multi-pin (the
bulk operand requires a positive order). Include the subsequent closure sector
histories where the edge removed didn't split this set.

Use finset→list and flatMap: multiplicities count. No extra division by the number-of-marks factorial
since we use named occurrences, and these Glade slots are connected-cumulant
sources. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect High Latch Job Rake Geo Tone Momentum Osc Snap Fiddle Metric
open scoped Topology ContDiff
namespace Planted
variable {G : Gauge} {I J W : Type} [LinearOrder W] {b : Bool} {n : ℕ} {R T : ℝ}

abbrev Script (G:Gauge) := Σ h:ℕ, Convolve.T (LocalVertex G false h)
abbrev Jar (G:Gauge) (I:Type) := Σ b:Bool, Plan G I b
abbrev Opus (G:Gauge) (I W:Type) := Finset W→ℕ→Plan G I true

variable (V : Palette G)(K:W→ Script G)(x:Rake.Position W I)

def tray (L:Opus G I W) (S:Finset W)(n:ℕ): Jar G I := if 2 ≤ S.card then ⟨true, L S n ⟩ else
   ⟨ false, if hp:S.Nonempty then let T:=K (S.min' hp); (marked V T.2 n).map bed else [] ⟩

def MixJar (X Y:Jar G I)(A:I→QP) := Mix V X.2 Y.2 A

def MixSeg (L:Opus G I W)(S p:Finset W)(n:ℕ) :=
   (Finset.antidiagonal n).toList.flatMap fun i=> MixJar V (tray V K L p i.1) (tray V K L (S\p) i.2) (rootX x p - rootX x S)

def stepSchedule (L:Opus G I W)(S:Finset W)(k:ℕ) : Plan G I true := if 2 ≤ S.card then
   ((Domain.paths k 0).toList.flatMap fun i=> bulkMix V (L S i) (bulks V (k-i))) ++
   (picks S).toList.flatMap (fun p=> MixSeg V K x L S p k) else []

lemma short_year {S p:Finset W} {i:ℕ×ℕ}{k:ℕ}(he:p∈picks S)(hp:i∈Finset.antidiagonal k): p.card+i.1<S.card+k ∧ (S\ p).card+i.2 < S.card+k := by
   obtain ⟨hz,h_1,h_2,hz'⟩:= Rake.n_small he; obtain hq:= Finset.card_lt_card hz; obtain hT:=Finset.card_lt_card hz'; rw [Finset.mem_antidiagonal] at hp; omega

lemma cares {L P:Opus G I W}(S:Finset W)(k:ℕ) (hP : ∀ p i, Finset.card p+i<S.card+k → L p i=P p i) : stepSchedule V K x L S k= stepSchedule V K x P S k := by
   unfold stepSchedule; split; swap; · rfl
   apply congr_arg₂ (·++·)
   · refine flat_from _ _ _ (fun i h=>?_); rw [hP S _ (Nat.add_lt_add_left ( Finset.mem_Ico.mp ( Finset.mem_toList.mp h )|>.2) _)];
   refine flat_from _ _ _ (fun p hp=>flat_from _ _ _ (fun i hi=>?_)); obtain ⟨hx,hV⟩:= short_year (Finset.mem_toList.mp hp) (Finset.mem_toList.mp hi);
   unfold tray; rw [hP p i.1 hx,hP (S\p) i.2 hV]

private def lift_height (V:Palette G)(K:W→Script G)(x:Rake.Position W I) (u:ℕ) : Opus G I W:= Nat.strongRecOn u (motive:=fun _=> Opus G I W) (fun u f=>fun S k=> stepSchedule V K x (fun p i=> if hp:Finset.card p+i<u then f (p.card+i) hp p i else []) S k)

def rising (S:Finset W)(n:ℕ): Plan G I true:= lift_height V K x (S.card+n) S n

theorem planting (S:Finset W)(n:ℕ): rising V K x S n= stepSchedule V K x (rising V K x) S n:= by
   unfold rising lift_height; rw [ Nat.strongRecOn_eq ]; apply cares
   intro p i h; rw [dif_pos h]

/-- Enumerate the actual families at an arbitrary order and tuple index. -/
def atlas (S:Finset W) (n:ℕ) : Jar G I := tray V K (rising V K x) S n

def mesur (μ:ℝ)(S:Finset W)(n:ℕ) : Glade G I:= projectV 0 (nominal μ (atlas V K x S n).2)

lemma plane_chart (μ:ℝ){S:Finset W}(hs:2≤S.card)(n:ℕ): mesur V K x μ S n=projectV 0 (nominal μ (rising V K x S n)) := by unfold mesur atlas tray; rw [if_pos hs]

lemma plane_single (μ:ℝ)(i:W)(n:ℕ): mesur V K x μ {i} n=projectV 0 (nominal μ ((marked V (K i).2 n).map bed)) := by
   unfold mesur atlas tray; rw [if_neg (by simp : ¬ 2≤ ({i}:Finset W).card), dif_pos];
   · rw [Finset.min'_singleton]
   exact Finset.singleton_nonempty i

variable [TopologicalSpace I]
lemma scry {S:Finset W}(n:ℕ)(L:Opus G I W) (h:L S n|> Hired): Hired (tray V K L S n).2 := by
   unfold tray; by_cases he: 2≤S.card; rw [ if_pos he ]; exact h
   rw [if_neg he]; by_cases hh:S.Nonempty; rw [dif_pos hh]; next => intro i hi; obtain ⟨i,hi,rfl⟩:= List.mem_map.mp hi; trivial;
   rw [dif_neg hh]; exact hire_none


def MapGap (x:Rake.Position W I): Prop:=∀ i j:W,i≠j→ AdmittedGap (x i-x j)
variable (h:MapGap x) {L:Opus G I W}
include h

lemma roadGap {S p:Finset W}(he:p∈picks S): AdmittedGap (rootX x p-rootX x S):= by
   obtain ⟨_,hT,hQ,hP⟩:= Rake.n_small he; rw [unfT x he,rootX,rootX,dif_pos hT,dif_pos hQ];
   refine h _ _ (fun H=>?_); obtain hh:= Finset.min'_mem (S\p) hQ; exact (Finset.mem_sdiff.mp hh).2 ( H ▸ Finset.min'_mem p hT )

lemma supply_mix (S k: Finset W) (n:ℕ) (hp:∀ p i, Finset.card p+i<S.card+n → Hired (L p i))(hk:k∈picks S): Hired (MixSeg V K x L S k n) := by
   refine hire_over _ (fun i hi=>?_); obtain ⟨hx,hξ⟩:= short_year hk (Finset.mem_toList.mp hi); exact hire_pin _ _ _ (scry V K _ _ (hp _ _ hx)) (scry V K _ _ (hp _ _ hξ)) (roadGap x h hk)
lemma supply_step (S:Finset W)(n:ℕ)(hp:∀ p i, Finset.card p+i < S.card+n→ Hired (L p i)): Hired (stepSchedule V K x L S n):= by
   unfold stepSchedule; split; swap; · exact hire_none
   refine (hire_append _ _).mpr ⟨ hire_over _ (fun i hi=> hire_b V (bulks V (n-i)) (L S i) (hp _ _ ?_)), hire_over _ (fun i hi=> supply_mix V K x h _ _ _ hp (Finset.mem_toList.mp hi))⟩
   obtain hh:= (Finset.mem_Ico.mp (Finset.mem_toList.mp hi)).2; omega
lemma hired_all (S:Finset W)(n:ℕ) : Hired (rising V K x S n):= by
   generalize hu:S.card+n=u
   induction u using Nat.strong_induction_on generalizing n S with
   | h u ih=> rw [planting]; exact supply_step V K x h S n (fun p i hp=> ih _ ( hu ▸ hp ) _ _ rfl)
lemma atlas_hired (S:Finset W)(n:ℕ) : Hired (atlas V K x S n).2 := scry V K n _ (hired_all V K x h S n)
end Planted
end YM.MS.ScaleForest
