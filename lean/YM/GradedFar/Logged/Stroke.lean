import YM.GradedFar.Logged.Docks
/-!
# Fixed cost of each rotated bracket (`Receipts.fit_old` and `fit_tint` adaptations)

With true hierarchy continuation identities & through-shadow-old; keep all weights
and log exponents at compact separation. Important: none of these are estimates on
rescaling the actual vertices at H yet, use them for any physical basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Logged.Stroke
open Finset Filter Function Set Spec Table Extraction OPE.Log Orbits
open scoped Topology Classical BigOperators
attribute [local instance] YM.Work.A15.compact_ortho
open Economy (Paint)
open private discrepancy_flip flip_cost from YM.OPE.Orbits.Rent
variable {G:Gauge}{C:Family G}{f:Order}{S:Table C.book}
    (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {I J L:Type} [Fintype I] [Fintype J] (K:Economy.Small L) {M δ:ℝ}(hm:0≤M)(hd:0<δ)
    (x:L→I→E4)(z:L→E4) (hx:∀ᶠ i in K.p,WithinRoom (K.r i) M δ (x i) (z i))
    {d:I→ℕ} {e:J→ℕ}
    (bank : LogTrace F R.port)
local notation "Q"=>F.sector.derivatives
local notation "X"=>F.sector.turns
local notation "P"=>R.port
local notation "r"=>K.r
local notation "ρ"=>F.room.kernel.spin

/-- HorizonFork normalized power for fresh-vs-cut. -/
abbrev lifetime (d:I→ℕ)(v:ℕ)(t:ℝ):= t^(v+1)/t^(∑ j, d j)

section kept
variable (v: Labels S d) (s:L→Viewers F)
variable (m:ℕ) (y:L→J→E4){c:ℝ}(hc:0<c)(hy:∀ᶠ l in K.p,ClearOf (z l) (y l) c)
local notation "ζ"=>fun l:L=>shadowOld R.port m (x l) (z l) v

include bank hx hd hm hy hc
lemma orders_far :
    (∀ᶠ i in K.p, Injective (beside (x i) (y i)) ∧ Injective (beside (sole (z i)) (y i))) ∧
    ∀ w:Labels S e, Paint K (lifetime d m ∘ K.r)
      (fun i=> discrepancy (spectator F (s i)) m (x i) (z i) v (ζ i) (y i) w) := by
    have hp (w : Labels S e) : ∃ k:ℕ, ∀ᶠ i in K.p, Injective (beside (x i) (y i)) ∧ Injective (beside (sole (z i)) (y i)) ∧
          Tested F R.port m (x i) (names v) (z i) (y i) (names w) (badge (r i)^k * lifetime d m (r i)) := by
       obtain ⟨k,h⟩:= bank.horizons I J (names v) (names w) δ M c hd hm hc m
       refine ⟨k,?_⟩; filter_upwards [hx, hy,K.leaps.eventually h] with i hx hy hi using hi (x i) (y i) (z i) hx hy
    constructor
    · obtain ⟨k,h⟩:= hp (fun i=>0); exact h.mono fun i hi=> ⟨hi.1,hi.2.1⟩
    intro w; obtain ⟨k,h⟩:=hp w; refine Paint.from_cost 1 zero_lt_one k ?_
    filter_upwards [h] with i h; rw [one_mul]
    rw [discrepancy_old ..]; exact h.2.2.phaseBound _
    · exact spectate F (s i)
    · exact spectate_respects F (s i)
    · exact spectate_ready F (s i)
    exact h.2.1

lemma old_moving_cost (w:L→Labels S e)(hw:∀j:J, Paint K (fun _=>1) (fun l=>w l j)) :
    Paint K (lifetime d m ∘ K.r) (fun i=> discrepancy (spectator F (s i)) m (x i) (z i) v (ζ i) (y i) (w i)) := by
    let T:=fun i=> spectator F (s i); let f i:= discrepancy_flip (T i) m (x i) v (z i) (ζ i) (y i) (e:=e)
    obtain ⟨hh,h⟩:= orders_far F R K hm hd x z hx bank v s m y hc hy (e:=e)
    have he : ∀ w:L→Labels S e,∀ᶠ i in K.p,f i (w i)=discrepancy (spectator F (s i)) m (x i) (z i) v (ζ i) (y i) (w i):=
      fun w=>hh.mono (fun i h=> (flip_cost _ _ _ _ _ _ _ _ (spectate F (s i)) h.1 h.2).symm )
    have hz:= Economy.Paint.contract («P»:=lifetime d m ∘ K.r) f (fun u=> (h u).assists (Filter.EventuallyEq.symm (he (fun _=>u)))) (fun _ _=>1) w hw
    simpa only [Finset.prod_const_one,one_mul] using hz.assists (he w)
end kept
section spin
variable (v: Labels S d) (k:L→Ortho)
include F R
lemma pebble (e:Exterior C.book) : ∀ j:Fin e.n, Paint K (fun _=>1) (fun i=> turnsPort F.sector.turns (k i) e j) := by
    intro i; obtain ⟨b,h⟩:= isCompact_univ.exists_bound_of_continuousOn (R.law.spin _ (fields _ e i)).continuousOn
    exact Paint.bounded b (Eventually.of_forall fun i=> h (k i) (mem_univ _))
lemma conforms (e:Mode F.sector.derivatives)(m:ℕ) : Paint K (fun _=>1) (fun i=> F.sector.turns.act m (k i) (R.port.loaded e m)) := by
    obtain ⟨b,h⟩:= isCompact_univ.exists_bound_of_continuousOn (R.law.spin m (R.port.loaded e m)).continuousOn
    exact Paint.bounded b (Eventually.of_forall fun i=> h (k i) (mem_univ _))
include hm hd hx bank
lemma spun (m:ℕ)(e:Exterior C.book) : Paint K (lifetime d m ∘ K.r) (fun i=>singleError F R m x z v i e (k i)) := by
    obtain ⟨c,hc,h⟩:= Dock.turned e
    exact old_moving_cost F R K hm hd x z hx bank v (fun _=>none) m _ hc (Eventually.of_forall fun i=>h (k i) (z i)) _ (pebble F R K k e)

-- conjugation form with costs of all the same labels
lemma tint (m:ℕ)(e:Exterior C.book) : Paint K (lifetime d m ∘ K.r) (fun i=> errorColor F R m x z v i e (k i)):= by
    obtain ⟨c,hc,h⟩:= Dock.turned e
    let y:= fun i=>swung e (k i) (z i); let w:=fun i=>turnsPort X (k i) e
    have hi : ∀ᶠ i in K.p, ClearOf (z i) (y i) c := Eventually.of_forall fun i=>h (k i) (z i)
    let Z:=fun i=> shadowOld R.port m (x i) (z i) v
    have hw:∀ j, Paint K (fun _=>1) (fun l=> (bar ρ (w l)) j):= fun j=> Paint.linear_r (conjugateR ρ (expo e j)) ((pebble F R K k e) j)
    have hz:= old_moving_cost F R K hm hd x z hx bank v (fun _=>none) m _ hc hi (fun i=>bar ρ (w i)) hw
    apply Paint.of_le hz; filter_upwards [(orders_far F R K hm hd x z hx bank v (fun _=>none) m _ hc hi (e:=expo e)).1] with i hi
    unfold errorColor; change ‖discrepancy S m (x i) (z i) (bar ρ v) (S.conj ρ m (Z i)) (y i) (w i)‖ ≤ ‖discrepancy S m (x i) (z i) v (Z i) (y i) _‖
    unfold discrepancy
    let R:= Orbits.whole S (x i) v (y i) (bar ρ (w i)); let Q':= Orbits.whole S (sole (z i)) (sole (Z i):Labels S (fun _:Unit=>m)) (y i) (bar ρ (w i)); change _ ≤ ‖R-Q'‖
    rw [← norm_star (R-Q'),star_sub]; apply le_of_eq; congr 1
    have hh:= whole_bar (v:=v) (w:=bar ρ (w i)) ρ F.room.kernel hi.1; have ht:= whole_bar (v:=fun _=>Z i) (w:=bar ρ (w i)) ρ F.room.kernel hi.2
    rw [bar_bar] at hh ht; exact congrArg₂ (·-·) hh ht
end spin
end YM.OPE.Logged.Stroke
