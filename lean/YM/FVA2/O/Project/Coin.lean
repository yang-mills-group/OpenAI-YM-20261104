import YM.FVA2.O.Project.Vault
/-!
# Balanced projection identity on weight-horizon lamps
 Applies before tests, in actual graded labels. Spectator arity arbitrary.
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
variable { G:Gauge }{ n m d k : ℕ }{a:ℝ}{q:Cn}{A: Album G}
variable {u:Scan G n}{v: Scan G m}{ T U:Cast G }{x:Points n}{y:Points m}
variable {b z:Bill G}{c:Draft G n}{ i:Grade G k }{f:Fable G n}
lemma party_h (A:Album G)(T:Cast G)(u:Scan G n)(v:Scan G m): party ( marking T A ) x y u v= concert T u (fun j=> concert T v ( party A x y j )):= splits ..
abbrev tour (A:Album G)(d:ℕ)(y:Points m)(v:Scan G m)(b: Grade G d):= lonelyG A y ( own b ) v
lemma spec (i:Grade G d): tour ( marking T A ) d y v i=∑ j:Grade G d, T d i j * concert T v (fun p=> tour A d y p j):= by
    unfold tour lonelyG; rw [ party_h, Score.solo ]
abbrev pipes (T:Cast G)(A:Album G)(d:ℕ)(y:Points m)(v:Scan G m): Grade G d→ Cn:= fun j=> concert T v (fun p=>tour A d y p j)
lemma table (d:ℕ): tour ( marking T A ) d y v = T d *ᵥ pipes T A d y v:= funext fun i=> spec i
lemma tag_a (A:Album G)(v:Scan G m)(b:Bill G)(d:ℕ): wage d A y v b= ( (fun k:Grade G d=> b ( own k )) ⬝ᵥ tour A d y v ):= rfl
-- finset sums mixed nondependent.Live. Utility economics exchange sum commuting inside concerts
variable {I:Type}
lemma concert_sum (v:Scan G n)(s:Finset I)(F:I→ Scan G n→ Cn) : ∑ i∈s, concert T v (F i)= concert T v (fun j=>∑ i∈s,F i j):= by unfold concert; simp_rw [Finset.mul_sum]; exact Finset.sum_comm
lemma concert_sum_r (v:Scan G n)(a:Cn)(F:Scan G n→ Cn): a*concert T v F= concert T v (fun j=> a*F j):= by unfold concert; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _=>mul_left_comm ..
lemma concert_sum_l (v:Scan G n)(a:Cn)(F:Scan G n→ Cn): concert T v F*a=concert T v ( fun j=> F j*a ):= by unfold concert; rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun _ _=> mul_assoc .. )
lemma concert_sub (v:Scan G n)(F L: Scan G n→ Cn): concert T v F-concert T v L= concert T v (fun j=>F j-L j):= by unfold concert; simp only [mul_sub, Finset.sum_sub_distrib]
lemma concert_k (T U:Cast G)(F: Scan G n→ Scan G m→ Cn): concert T u ( fun p=> concert U v ( F p ) )= concert U v ( fun r=> concert T u (fun j=> F j r )):= by unfold concert; simp_rw [ Finset.mul_sum ]; rw [ Finset.sum_comm ]; apply Finset.sum_congr rfl; intro j _; exact Finset.sum_congr rfl fun h _=> mul_left_comm ..
lemma assets (v:Scan G m)(d:ℕ): wage d ( marking T A ) y v b= concert T v ( fun w=> wage d A y w ( receipt T b ) ):= by
    rw [ tag_a, table, Matrix.dotProduct_mulVec ]; change (∑ i:Grade G d, receipt T b (own i) * pipes T A d y v i )=_; unfold pipes; simp_rw [ concert_sum_r, concert_sum v ]
lemma Lamp_flute (v:Scan G m)(h:ℕ): Lamp ( marking T A ) h y v b = concert T v ( fun w=> Lamp A h y w (receipt T b) ):= by
    change ∑ j∈Finset.range (h+1),wage j (marking T A) y v b=_; simp_rw [ assets, concert_sum ]
lemma wage_credit (c:Draft G n)(u: Scan G n): wage d A y v (fun i=> concert T u ( fun p=> c p i ))=concert T u ( fun p=> wage d A y v ( c p ) ):= by
    unfold wage Settle; simp_rw [ concert_sum_l ]; exact concert_sum ..
lemma Lamp_credit : Lamp A d y v ( fun i=> concert T u ( fun p=> c p i ))= concert T u ( fun p=> Lamp A d y v ( c p ) ):= by
    change ∑ j∈ Finset.range (d+1),wage j _ _ _ _=_; simp_rw [ wage_credit,concert_sum ]
lemma pocket (A:Album G)(h:Rooted q)(c:Bill G): Lamp ( tune q A ) d y v ( fun i=> ( c i ).subst q )=( Lamp A d y v c ).subst q:= by
    unfold Lamp Settle; unfold lonelyG party tune; rw [← coe_substAlgHom (Reg.Choice.licence q h),map_sum]; simp only [ map_mul,map_sum ]
lemma exchange (A:Album G)(h:Gift T q u c b)(hp:Rooted q): Basket ( marking T ( tune q A ) ) u v b d x y= concert T u (fun w=> concert T v (fun p=> ( Basket A w p ( c w ) d x y ).subst q ) ):= by
    unfold Basket; rw [ party_h, Lamp_flute, ← h ]; unfold credit; simp_rw [ Lamp_credit ]; rw [concert_k T T ( fun p w=> Lamp _ _ y p (fun i=> ( c w i ).subst q) ), concert_sub ]; simp_rw [ concert_sub v, pocket A hp, ← coe_substAlgHom (Reg.Choice.licence q hp), map_sub ]; simp_rw [coe_substAlgHom]
end YM.FVA2.O.Project
