import YM.GradedFar.Round.Scene

/-!
# Witnesses tying the C5 physical *hypotheses* to the measurements

Use to call C5 through the larger `Sec G h`; scope in document.
Statements `Ample`, `Grid` can use the displayed `Notice`/`Line` on exactly the
h used in C's call. `On` any fixed true horizon change etc.
-/
namespace YM.FVA2.GradedFar.Physical.Elevation
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open OPE Orbits Logged Physical.Round
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h k j t p d : ℕ} {I V:Type} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "ν"=>Teller.logNu 1
include H
-- even off Conf, because we use fxt (zero)
lemma line_up (x:Points n)(v:Tags G d n)(he:d≤h) : Pose.line N x v=Pose.line N x (up he∘v):= by
   ext i; unfold Pose.line; simp_rw [coeff_mk]; unfold Jury.fxt
   have a:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born; by_cases ht:x∈conf n
   · rw [dif_pos ht,dif_pos ht]; exact Scale.Measure.inherited N.scheme N.criterion ν M A simple a.Taylor a.still a.base he n _ _ _
   rw [dif_neg ht,dif_neg ht]; rfl
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (J : FramesH P)
    (hJ: oriented U J)
local notation "F"=> familyPoint U J
omit H in
lemma currentK (W:Filter I)(r:I→ℝ)(hr:Tendsto r W τ) (u:I→Points n) (hp:∀ᶠ i in W,u i∈conf n)(v: Tags G d n) (hd:d≤h)(hr':oriented U J) :
    ∀ᶠ i in W, F d (r i) n (u i) v= F h (r i) n (u i) (up hd ∘ v) := by
    filter_upwards [hr.eventually (hr'.raises d h hd),hp, hr.eventually self_mem_nhdsWithin] with i hi hp (hr:0<r i)
    exact painted_rise U J none (v:=v) (present hr hp) (d:=fun _=>d) (d':=fun _=>h) (fun _=>hd) (fun i=>hi _)
lemma ephemeral (x : Points 0) (v:Tags G d 0) : Pose.line N x v=1:= by
    have he:x∈conf 0:=fun i=>i.elim0; ext i; rw [Pose.line,coeff_mk,Jury.fxt,dif_pos he]; rw [← Subarray.book_empty H d ⟨x,he⟩ v]; exact (Subarray.status_empty d (Pose.Bbook N d 0 ⟨x,he⟩) (Measure.adjust N.scheme N.criterion d) v i).symm
omit H in
lemma vacuums (x:Points 0)(v:Tags G d 0) (s:ℝ): F d s 0 x v=1:= by
    change painted U J none (fun _=>d) s x v=1; rw [painted_cost U J none 0 s x v (by intro i; exact i.elim0), Orbits.observed]; exact card_zero_eq _ (spectate U none).laws _ _

-- alternative form for C5, prices genuine `≤ C'` & uniform over explicitly requested labels in compact, require ONLY true nonempty jobs (always stock at least 3). Full application using *any* assembled h≥6*, we can lower after the pricing. Money version calibrated. Use `familyPoint` all `W_r` here. Supports and Jobs chosen fixed.
def Answered (v : Tags G d n) (X:Set (Points n))(q k:ℕ) {h:ℕ}(he:d≤h)(θ':ℝ→ℝ)(D:ℝ→Normalize.Change G d):=
    0<n → ∃ C:ℝ, ∀ᶠ r in τ, ∀ x∈X,
     ‖familyPoint U J d r n x v- crop q (θ' r) (Pose.line N x (up he ∘ (stand (D r)∘v)))‖ ≤ C* gYM G r^k
lemma answers (v:Tags G d n) (X:Set (Points n))(q k:ℕ){h:ℕ}(he:d≤h)(θ':ℝ→ℝ)(D:ℝ→Normalize.Change G d)
    (hp:Answered N U J v X q k he θ' D): Confirmed N (F d) q k θ' D X v := by
    by_cases h:n=0
    · subst n
      unfold Confirmed; simp_rw [vacuums, ephemeral N M H]; simp only [crop, coeff_one];
      simp; exact Terms.blind (isBigO_zero ..)
    obtain ⟨C,hC⟩:=hp (Nat.pos_of_ne_zero h); apply Terms.of_bound C <;> filter_upwards [hC,positive_g simple] with r hi (hr:0<gYM G r)
    · intro j; rw [line_up N M H _ (stand _∘ v) he]; exact hi j.val j.property
    positivity
end
end YM.FVA2.GradedFar.Physical.Elevation
