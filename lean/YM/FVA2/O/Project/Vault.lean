import YM.FVA2.O.Bind.Stars
/-!
# Graded prices and invertible near-free scheme changes

On the actual alphabet and power series $Cn$, at any position and logarithmic
power. Output frame is block diagonal `cue`, used for contraction with ANY
observer list. The algebraic identities in this file apply *before* imposing
Ward/prices: they are just changes of labels and coupling. Assume no kernel at all.

Index convention for Cast = input first; so receipt computes $Z p_{out}$.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Project
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind
variable {G:Gauge}{ n m d k : ℕ }{a t:ℝ}{ q p:Cn }{ A:Album G }
variable {T U:Cast G}{x:Points n}{y:Points m}{ s:Set (Points n) }{o j:Q G}{u:Scan G n}{v:Scan G m}
abbrev Bill (G:Gauge):= Q G→ Cn
abbrev Draft (G:Gauge)(n:ℕ):= Scan G n→ Bill G
variable {b z: Bill G }{ c: Draft G n }
-- non-conjugating field conversion on outputs as actual slots
abbrev receipt (T:Cast G)(b:Bill G): Bill G := fun i=> ∑ j:Grade G (heft i), b (own j)*T ( heft i ) j i.item
abbrev receipts (T:Cast G)(b:Bill G)(d:ℕ): Grade G d→ Cn:= ((fun j:Grade G d=> b (own j)) ᵥ* (T d)) -- Matrix.vecMul
lemma receipt_apply (T:Cast G)(b:Bill G)(j:Grade G d): receipt T b ( own j )= receipts T b d j:= rfl
lemma timely (T U:Cast G)(b:Bill G): receipt U ( receipt T b )=receipt (T*U) b:= by
    funext q; rcases q with ⟨d,i⟩; change receipt U (receipt T b) ( own i )=_; rw [ receipt_apply ]; change receipts U (receipt T b) d i=receipts (T*U) b d i; unfold receipts; simp_rw [receipt_apply]; exact congr_fun (Matrix.vecMul_vecMul ..) i
lemma receipt_K : receipt 1 b=b:= by funext i; simp only [ receipt,Pi.one_apply,Matrix.one_apply,mul_ite,mul_one,mul_zero, Finset.sum_ite_eq',Finset.mem_univ,if_true ] -- if true
-- incoming concert + coupling f on all fees
abbrev credit (T:Cast G)(q:Cn)(c:Draft G n): Draft G n := fun u i=> concert T u ( fun p=> (c p i).subst q )
abbrev refund (T U: Cast G)(q:Cn)(c:Draft G n): Draft G n:= fun u=> receipt U ( credit T q c u )
/-- Comparison of pricing functions (transfer equation on physical labels) -/
def Gift (T:Cast G)(q:Cn)(v:Scan G n)(c:Draft G n)(e:Bill G): Prop:= credit T q c v=receipt T e
lemma rate (h:U*T=1): Gift T q u c ( refund T U q c u ):= by unfold Gift refund; rw [timely,h,receipt_K]
-- engineering powers R^{w-e}. `fee` notation $exp(-t*a)$
abbrev pack (u:Scan G n)(t:ℝ)(f:Bill G): Bill G:= fun i=> PowerSeries.C ( Score.fee t ((heft i:ℝ)-(totalG u:ℝ) ) )* f i
lemma expense (i:Q G) (v:Grade G (heft i)): ( ( heft ( own v ):ℝ )- (totalG u:ℝ) )=( ( heft i:ℝ )- (totalG u:ℝ) ):= rfl
lemma box_k (T:Cast G)(u:Scan G n): receipt T (pack u t b)= pack u t ( receipt T b ):= by
    funext i; unfold receipt pack; simp_rw [ Finset.mul_sum ]; exact Finset.sum_congr rfl fun _ _=> mul_assoc _ _ _ -- need just $fee*b*T = fee*(b..)$
lemma in_house {R:Cn}(p:ℂ)(b:Cn)(ht:Rooted R): (PowerSeries.C p * b).subst R= PowerSeries.C p * b.subst R:= by
    rw [ ← PowerSeries.coe_substAlgHom (Reg.Choice.licence R ht), map_mul,PowerSeries.coe_substAlgHom (Reg.Choice.licence R ht),PowerSeries.subst_C ]; rfl -- name
lemma pay_h (h:Rooted q): credit T q ( fun v=> pack v t ( c v ) ) u=pack u t ( credit T q c u ):= by
    funext i; unfold pack credit concert; simp_rw [ in_house _ _ h, Finset.mul_sum ]; exact Finset.sum_congr rfl (fun _ _=> mul_left_comm _ _ _ ) -- check parse
lemma Gift.total (he:Rooted q)(hp: Gift T q u c z): Gift T q u (fun v=> pack v t ( c v ) ) ( pack u t z ):= by unfold Gift; rw [pay_h he, hp, box_k]
-- commute tune with weight fee * tune on Lamp. encaps identity for fps proof.
end YM.FVA2.O.Project
