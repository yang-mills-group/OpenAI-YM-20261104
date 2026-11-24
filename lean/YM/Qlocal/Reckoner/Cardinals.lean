import YM.Qlocal.Reckoner.Stamp
/-! Selling a persistent receipt: common K, any regrouping only when exposed ready.
 Log arrays retain old and new mark traces explicitly, including field-independent
 Magma and errors — no subtraction of unaligned kernels later. Publishable
 with the specialized tests/position incidences when Economy attested.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Reckoner
open Function RG Lattice Wilson Pert.Attach MeasureTheory Filter Progress.DirectedRecipe Finset
open Marker RG03.Gather Push.AbsoluteSums RG3.Press
open scoped Topology ContDiff BigOperators Classical
open Publishing Parabola Integration.RiderTastePresentation Integration.LocalComparison Extra.Trajectories
variable {V Ω J J' J₀ K α:Type}[DecidableEq V]{G:Gauge}{n:Side}{R:Census V}
variable {X: RG.Rep G n}{s:V→ Support n}{q q':Ray R} {A A' B B' u v a r t w δ:ℝ} {o: V→Site n}
namespace Scribe
variable {S:Scribe Ω J G n R} {T:Scribe Ω J' G n R} {p:BudgetPoint} {L:Loom K R n}
    (F:Lot K S L) 
noncomputable def paired_lot (L:Loom K R n) (S T:Scribe Ω K G n R)
    (h:S.tag=L.tag) (he:T.tag=L.tag) (hx:∀ i,S.region i⊆L.region i) (hy:∀ i,T.region i⊆L.region i): Lot K (S.pile T) L where
  rows:=fun i=>{Sum.inl i,Sum.inr i}
  singly:=by intro i j u hu hv; rw [mem_insert, mem_singleton] at hu hv; rcases hu with rfl|rfl <;> rcases hv with hv|hv <;> injection hv <;> assumption
  logic:= by
    intro i u hu; rw [mem_insert, mem_singleton] at hu; obtain rfl|rfl:=hu; exact congr_fun h i; exact congr_fun he i
  cost:=by intro i u hu; rw [mem_insert, mem_singleton] at hu; rcases hu with rfl|rfl; exact hx _; exact hy _
lemma Lot.earn_all (ht:∀ i,F.runs i) : F.sought= S:=by unfold Lot.sought eligible; simp only [ht,if_true]
abbrev selects (P:Ray R → ℝ) (t:R.Mode) := P (Pi.single t 1)
noncomputable abbrev weather (o:V→Site n)(s:V→Support n)(X:RG.Rep G n)(S:Scribe Ω J G n R)(K:Source G n Ω R) [Countable J][Nonempty V]:= (S.printP K).taste X o s

variable [Fintype V]
-- without needing [Countable], and for any post presentation Power.
noncomputable def density (X:RG.Rep G n)(S:Scribe Ω J G n R)(K:Source G n Ω R)(x:Ω)(U:Config G n): Poly R:= (Real.exp (X.exponent U):ℂ) • session X.p X.activities (K x) (S.send X.p x) U
variable {K':Source G n Ω R}
lemma reorder (h: S.send X.p=T.send X.p) : Scribe.density X S K'= Scribe.density X T K':= by unfold density; rw [h]
variable (hr: Rental q) (h0:S.Proper X.p s)(h1:T.Proper X.p s)(hK:Night X s K' q t B)(hS:S.Spend X.p q t A)(hv:T.Spend X.p q t A')(ht:0≤t)
include hK h0 hS hr ht
lemma prints [Countable J][Nonempty V] (hg:∀ i,o i∈s i) (x:Ω): S.density X K' x = ((weather o s X S K').leaf x).density:= by
 funext U; let hQ:=Scribe.Night.bulk h0 hS hK hr; let he:= S.authentic h0 hg hK.policy
 let y:= Parabola.published (S.printP K') he hr ht hQ x U; rw [show markRead (r:=X) (S.printP K') x=S.send X.p x from funext (S.marked K' x)] at y; exact y.symm
omit hK
include h1 hv
lemma pile_density (K:Source G n Ω R)(x v): (S.pile T).density X K x v= Poly.pass (S.send X.p x v)* T.density X K x v:= by
 unfold density session; rw [pool h0 h1 hS hv hr ht, pass_add (Scribe.calm_send hS hr h0 ht ..) (Scribe.calm_send hv hr h1 ht ..), mul_smul_comm, mul_assoc]
lemma unchanged [Countable J][Countable J'][Nonempty V] (h:Night X s K' q t B) (he:∀ x,S.send X.p x=T.send X.p x) (hg:∀ i,o i∈s i) : ∀ x, ((weather o s X S K').leaf x).density=((weather o s X T K').leaf x).density := by intro x; rw [← prints hr h0 h hS ht hg,← prints hr h1 h hv ht hg,reorder (funext he)] -- args order
-- Bundle consumption.K.Inference.Invoice Budget | Heat ≥ P*. Includes security at extra expense. Real Rég.Comp.Ch log/res.
end Scribe
open Scribe
-- no need o until handing to `.Peak`.
structure Certified (X:RG.Rep G n)(s:V→ Support n)(r:Ray R)
    (a v m j z:ℝ) (S:Scribe Ω J G n R) (E:Scribe Ω J' G n R)(T:Scribe Ω J₀ G n R) (K: Source G n Ω R) [Fintype V] (W:Ω→ Config G n→Poly R) : Prop where
 model_ok : S.Proper X.p s
 model_spend : S.Spend X.p r a m
 error_ok : E.Proper X.p s
 error_spend : E.Spend X.p r a j
 rough_ok : T.Proper X.p s
 rough_spend : T.Spend X.p r a z
 hard : Night X s K r a v
 sales : Scribe.density X (S.pile (E.pile T)) K=W
-- budgets in unified r. In the primitive compiler prefer exposing multiple weights (shrunken r on hard, clock Q≥r on some others). Keep form in Status.Alpha.
-- Can specialize & reshape.Express forecast representation alternating long & mask.
variable [Fintype V]
variable {S:Scribe Ω J G n R} {T:Scribe Ω J₀ G n R}{E:Scribe Ω J' G n R}{K':Source G n Ω R}{W:Ω→ Config G n→Poly R}
    (h:Certified X s q a v A B w S E T K' W)(hp:Rental q)(ht:0≤a)
    (F:Scribe Ω K G n R)
    (hv:F.Proper X.p s)(hs:F.Spend X.p q a u)
include h
lemma Certified.limit (p: Rental q') (he:q' ≤ q): Certified X s q' a v A B w S E T K' W:=
  {h with model_spend:= h.model_spend.narrower p he, error_spend:= h.error_spend.narrower p he, rough_spend:= h.rough_spend.narrower p he, hard:= Reckoner.Night.narrow h.hard p he le_rfl}
include hp ht hv hs
lemma Certified.extend : Certified X s q a v (A+u) (B+u) w (pile S F) (pile E F.discount) T K' W:=by
 refine {h with model_ok:=Proper.pile h.model_ok hv, model_spend:= Spend.pile h.model_spend hs, error_ok:= Proper.pile h.error_ok (hv.shade _), error_spend:=Spend.pile h.error_spend hs.discount, sales:=?_}
 rw [← h.sales]; apply reorder; funext x U; let h₀:= Proper.pile h.model_ok hv; let h₁:=Spend.pile h.model_spend hs; let h₂:= Proper.pile h.error_ok (hv.shade (fun _ _=>-1)); let h₃:= Spend.pile h.error_spend (hs.discount); let h₄:=h.rough_ok; let h₅:=h.rough_spend;
 rw [pool h₀ (h₂.pile h₄) h₁ (Spend.pile h₃ h₅) hp ht, pool h.model_ok hv h.model_spend hs hp ht,pool h₂ h₄ h₃ h₅ hp ht,pool h.model_ok (h.error_ok.pile h₄) h.model_spend (Spend.pile h.error_spend h₅) hp ht,pool h.error_ok h₄ h.error_spend h₅ hp ht]; let h':Proper F.discount X.p s:= hv.shade _; rw [pool h.error_ok h' h.error_spend hs.discount hp ht,send_discount]; abel
-- E= total signed Δ including masks. Must not use its own forced comparing to Model.We.Norm.We print preserving.
omit F hs hv
variable [Nonempty V] [Countable J][Countable J'][Countable J₀]
lemma Certified.tally (hg:∀ i,o i∈s i):
  let T':=weather o s X (pile S (pile E T)) K'; Peak X o T' q a (A+(B+w)) v ∧ RetainsDeclared (Declared X s R) T' s ∧ ∀ x:Ω,(T'.leaf x).density = W x:= by
  intro T'; let he:= h.model_ok.pile (h.error_ok.pile h.rough_ok); let hv:= (pile S (pile E T)).authentic he hg h.hard.policy; let ht':= Scribe.Night.bulk he (Spend.pile h.model_spend (Spend.pile h.error_spend h.rough_spend)) h.hard hp
  refine ⟨assemble hv q hp.oneSize ht', Publishing.retains_ hv, fun x=> ?_⟩; exact ((Scribe.prints hp he h.hard (Spend.pile h.model_spend (Spend.pile h.error_spend h.rough_spend)) ht hg x).symm).trans (congr_fun h.sales x)
end YM.Qlocal.Reckoner
