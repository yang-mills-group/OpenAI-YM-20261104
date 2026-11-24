import YM.MS.ScaleForest.Sense
/-!
# All closures of a placed frame, recover in the *actual position* recurrence

Sum over all-line colors, every rank covered, multiplicities given explicitly.
Do not ascribe to a single rooted history the cost of the official `Trip`
problem. It is the forest sum that makes the necessary telescope. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect High Latch Job Rake Geo Tone Momentum Osc Snap Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I J: Type} {F H:Curtain G I} {μ:ℝ} {X:Glade G I}
lemma zeroTimeSeen (hf:Seen F)(hh:Seen H)(K:LineRule G)(μ:ℝ): Ufor K μ (F+H) 0= (Ufor K μ F+Ufor K μ H) 0:= funext fun t=>funext fun i=> loopPlus K pit (hf i t) (hh i t) _

namespace Planted
abbrev Plan (G:Gauge) (I:Type)(b:Bool) := List (Planted G I b)
variable {b : Bool} {L R:Plan G I true} {k:ℕ}
def nominal (μ:ℝ)(L : Plan G I b): Curtain G I:= (L.map (resolve μ)).sum
def interests (μ:ℝ)(L : Plan G I true): Curtain G I := (L.map (push μ)).sum

variable (μ)
lemma nom_sum (X Y:Plan G I b): nominal μ (X++Y)= nominal μ X+nominal μ Y:= by simp [nominal]
lemma share_sum (X Y:Plan G I true): interests μ (X++Y)=interests μ X+interests μ Y:= by simp [interests]

variable [TopologicalSpace I]
abbrev Hired (L:Plan G I b):= ∀ i∈L,i.Stand
lemma hire_append (X Y:Plan G I b): Hired (X++Y) ↔ Hired X ∧ Hired Y:= by unfold Hired; simp [or_imp, forall_and]
lemma hire_cons (X:Planted G I b)(L: Plan G I b): Hired (X::L)↔X.Stand∧ Hired L:= by simp [Hired,or_imp,forall_and]
lemma hire_over {L:List J}(f:J→ Plan G I b)(hf:∀ i∈L, Hired (f i)) : Hired (L.flatMap f):= by intro i hi; obtain ⟨j,hj,hh⟩:= List.mem_flatMap.mp hi; exact hf j hj i hh
lemma hire_none : Hired ([] : Plan G I b):= by simp [Hired]

variable [FirstCountableTopology I]
lemma sit_seen (X:Planted G I b)(h:X.Stand): Seen (resolve μ X):= by obtain ⟨R,hR,hT,hX⟩:= (X.offers μ h).2.1 (1/2) (by norm_num) (by norm_num); exact fun i t=>hT.forms _ hR.top t i
lemma co_visible (L:Plan G I b)(hu : Hired L) : Seen (nominal μ L):= by apply Seen.list; intro i hi; obtain ⟨ j,hj,rfl⟩:= List.mem_map.mp hi; exact sit_seen μ j (hu j hj)

def profit (μ:ℝ)(L:Plan G I true) : Glade G I:= projectV 0 (interests μ L)-projectV 0 (Ufor (fullShell G) μ (nominal μ L))
omit [FirstCountableTopology I] [TopologicalSpace I] in
lemma profit_z : profit μ ([]:Plan G I true)=0:= by
   have hp : Ufor (fullShell G) μ (nominal μ ([]: Plan G I true))=0:= by funext z t x; exact closeG_zero ..
   unfold profit; rw [hp]; simp only [interests,List.map_nil,List.sum_nil,map_zero,sub_self]

lemma profit_sum (h : Hired L)(he : Hired R) : profit μ (L++R)= profit μ L+profit μ R:= by unfold profit; rw [share_sum,nom_sum,map_add, projects _ (zeroTimeSeen (co_visible μ L h) (co_visible μ R he) _ _),map_add ]; abel
lemma profitFlat {L:List J}(f:J→Plan G I true)(hf:∀ i∈L,Hired (f i)) : profit μ (L.flatMap f)=(L.map (fun p=> profit μ (f p))).sum := by
   induction L with
   | nil=> exact profit_z _
   | cons i l ih=> obtain ht : ∀ j∈l,Hired (f j):=fun j hj=> hf j (List.mem_cons_of_mem _ hj); rw [List.flatMap_cons,List.map_cons,List.sum_cons,profit_sum μ (hf i (by simp)) (hire_over f ht), ih ht]

-- roots up to all possibly occupied arities

def overline (P:Palette G) : ℕ→ Planted G I true → Plan G I true
 | 0, X=> [X]
 | k+1, X=> X::P.lines.flatMap (fun K=> overline P k (U K X))

variable (V:Palette G)(X:Planted G I true) (h:X.Stand)
include h
omit [FirstCountableTopology I] in
lemma lineup (n:ℕ): Hired (overline V n X):= by induction n generalizing X with | zero=>exact (hire_cons ..).mpr ⟨ h, hire_none⟩ | succ k ih=> rw [overline,hire_cons]; exact ⟨h,hire_over _ (fun i _=> ih _ h)⟩
lemma daylight (hk:X.slots<2*k+2) : profit μ (overline V k X)= projectV 0 (push μ X):= by
   induction k generalizing X with
   | zero=>
      rw [overline,profit, nominal, interests]; simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero];
      obtain hc:=X.offers μ h; obtain ⟨R,hR,hT,hX⟩:=hc.1 rfl (1/2) (by norm_num) (by norm_num)
      have hp (K:LineRule G) (t:ℝ) (i:I) : closeG K.half 0 (μ+t) (resolve μ X 0 t i)=0 := by
         obtain ht:= hT.forms _ hR.top t i; obtain he:= goods_o ht (K.ok.forms false) pit (hT.funds _ hR.top t i); funext m l; rw [closeG_eq,Pi.smul_apply,Pi.smul_apply,ranks_off he l (by norm_num at hk; omega), smul_zero]; rfl
      rw [projects 0 (show Ufor (fullShell G) μ (resolve μ X) 0=(0:Curtain G I) 0 from funext fun i=> funext fun t=>hp _ _ _), map_zero, sub_zero]
   | succ k ih=>
      have hh (K:LineRule G) : (U K X).slots < 2 * k + 2:= by unfold Planted.slots; omega
      have ht : ∀ i: LineRule G, profit μ (overline V k (U i X)) = projectV 0 (Ufor i μ (resolve μ X)):= fun i=> ih _ h (hh i)
      let f (K:LineRule G):= overline V k (U K X); let U:= V.lines.flatMap f
      rw [show overline V (k+1) X=[X]++U from rfl, profit_sum μ (by simpa only [Hired,List.mem_singleton,forall_eq] using h) (hire_over f (fun i hi=> lineup V (Planted.U i X) h _)), show profit μ U= _ from profitFlat μ f (fun i hi=>lineup V (Planted.U i X) h _)];
      unfold f; simp_rw [ht]; unfold profit interests nominal; simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero];
      rw [ ← projects 0 (palU V μ (sit_seen μ X h)), map_list_sum (projectV 0), List.map_map ]; exact sub_add_cancel ..
end Planted
end YM.MS.ScaleForest
