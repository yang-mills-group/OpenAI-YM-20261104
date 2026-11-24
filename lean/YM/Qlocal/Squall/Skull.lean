import YM.Qlocal.Squall.Purple
import YM.Qlocal.Versal.Warden
import YM.Qlocal.BaubleDesk
import YM.RGComparison01.Marks.Fiord
/-!
# Payment structure at manuscript tolerance.
 After a local stowed projection by spending its Lease. Poly in fine monitor for rents, mark wage. Rate remains only β^ε slack for Glory output.Diff.Owner.New.R.Use.Window Level.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Squall
open Filter Function Set Lattice Wilson RG Pressure Tree Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset Extra.Iteration Song
open Collection Quotes Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Roost Coat
open RGComparison01 RGComparison01.Pledge RGComparison01.Pledge.Holdings
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
namespace Skull
open Quipu Quipu.Sonnet Tern AllOrder AllOrder.Catch
variable {s : ℝ}{G:Gauge}{L: Side} {τ Y : ℝ} {P : Patch}
variable (G L) (ζ t:ℝ)(r z w:ℕ)(P:Stage) (J:Bauble G L)
set_option quotPrecheck false
local notation "f"=> betaF G t L
noncomputable abbrev Wage (A:ℝ) (Z:Stage)(w:ℕ)(g:ℝ):= 1+ (Real.exp Z.supportExponent)*(w:ℕ)*|A| * |g|
-- `[update]` expected args.Nat * casts.
noncomputable abbrev guest (a:ℝ)(x:ℝ):= Wage (J.invZ x) P w a
lemma wage_gs (x a:ℝ): 1 ≤ guest G L w P J a x:= by unfold guest Wage; apply le_add_of_nonneg_right; positivity -- `positivity` maybe shows 1 not!
lemma totals (W:ℝ→ℝ)(h:Geo G L W) : Geo G L (fun s=> guest G L w P J (W s) s):= (Geo.fixed 1).joins (((Geo.fixed _).times (Geo.mean J.positive)).times h.mean)
variable {p:BudgetPoint} {α:Type}[Fintype α] (u v:ℝ)

lemma seats (hx:0 ≤ v)(hu:0< J.mass u) (hJ:J.invZ u =(J.mass u)⁻¹)(ht:Time.Same P p)(hk:Fintype.card α ≤ w): let y:= guest G L w P J v u; Real.exp p.supportExponent * (∑ _i:α,y⁻¹ * v) ≤ J.mass u:= by
 intro y; have h: 0< y:= zero_lt_one.trans_le (wage_gs ..); let m:= J.mass u; let u':=Real.exp P.supportExponent; have hx':y=1+u'*w*m⁻¹*v:= by unfold y guest Wage; rw [hJ,abs_of_pos (inv_pos.mpr hu),abs_of_nonneg hx]
 rw [ht.2.2] -- `Same` .2.2 (not projection)
 apply le_of_mul_le_mul_right _ h; apply le_of_mul_le_mul_right _ (inv_pos.mpr hu); change _ ≤ m*y*m⁻¹; rw [mul_right_comm m, mul_inv_cancel₀ hu.ne',one_mul,sum_const, card_univ, nsmul_eq_mul]; let u1:= Real.exp P.supportExponent; have he : (Fintype.card α:ℝ)* (y⁻¹ * v) * y= (Fintype.card α:ℝ)*v:= by field_simp; -- use rewriting
 change u1*( _ * (y⁻¹*v))*y*m⁻¹ ≤ y; rw [mul_assoc u1 _,he]
 calc _ ≤ u1*((w:ℝ)*v)*m⁻¹:= by have h0 : 0≤ u1:=Real.exp_nonneg _; have hz:m>0:=hu; gcongr
      _ ≤ _ := by rw [hx']; unfold u' u1; linarith
noncomputable def score (r : ℕ): ℝ:= graded (r+1)
def orders (r:ℕ):ℕ:= 2*(r+1)
noncomputable abbrev platform (v:ℝ)(r:ℕ):ℝ:= score r + v
-- variable raw unit reserve x
abbrev tone (G:Gauge)(L:Side)(t v:ℝ)(r:ℕ):= betaF G t L ^ (platform v r)
noncomputable abbrev rise (r:ℕ):= J.roi t / (PhysicalNext.Repeat.Height.grow G L t)^(orders r)
noncomputable abbrev rescue (r:ℕ):= betaF G t L ^ (score r) + |rise G L t J r|
noncomputable abbrev vespers (r:ℕ):= rise G L t J r + rescue G L t J r
open ThroughLaunch
lemma risen : Rate G L (score r) (fun x=> Skull.rise G L x J r):= by
 let Z x:= -(3/8:ℝ)*(orders x); refine (J.revenue.rate.mul (Rate.power (a:=Z r))).weaken ?_ |>.congr ?_
 · unfold score Z graded orders; push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) r]
 filter_upwards [Delay.shift_pos G L] with t ht; unfold rise PhysicalNext.Repeat.Height.grow Z; rw [Real.rpow_mul (le_of_lt ht),Real.rpow_neg (le_of_lt ht),Real.rpow_natCast, inv_pow,← div_eq_mul_inv]
lemma fiscal : Rate G L (score r) (fun x=>vespers G L x J r):= (risen G L r J).add (Rate.power.add (Rate.compare (risen G L r J) (Eventually.of_forall fun i=> (abs_abs _).le)))
local notation "Z"=>Fiord.room z t
local notation "M"=>Fiord.amp z t
local notation "Y"=>Fiord.popG z t
local notation "S"=>Trio.fence z (Pressure.radiusB t) 0
local notation "b"=> tone G L t ζ r
noncomputable abbrev district := Leasing.zone P.order S b (vespers G L t J r)
lemma brighten (ht:b≥0)(hv:0<f) : 0≤ district G L ζ t r z P J:= by
 let a:=rise G L t J r; let gx:= (f^score r); have he:0 < gx:= Real.rpow_pos_of_pos hv _
 have hy:0 ≤ vespers G L t J r:= by change 0≤a+(gx+|a|); linarith only [he,neg_le_abs a]
 unfold district Leasing.zone Boulevard.ticket; positivity
lemma finial (hx:0≤ ζ): Rate G L (platform ζ r) (fun t=> district G L ζ t r z P J):= by
 let g:=fun i=> Skull.tone G L i ζ r; have hz: Rate G L (platform ζ r) (fun t=>Fiord.popG z t * vespers G L t J r):= ((Trio.feeStars G L z 0).mul (fiscal G L r J)).weaken (by simpa only [zero_add,platform] using le_add_of_nonneg_right (a:=score r) hx)
 have hT: Rate G L (platform ζ r) g:= Rate.power -- power lemma
 exact (((((hT.add hT).mul_left _).mul_right _).add (hz.mul_left _)).add (hT.add hz))
-- multiply by Rotunda.price & expenditure for mask alignment tent before use future support.Shape.State.We
noncomputable abbrev wave := Rotunda.priceP (Loads.size P 0) (2*M) (Z+M)
lemma floe : Geo G L (fun t=> wave t z P):= Fiord.motoring ..
local notation "T"=> Rotunda.priceP p (2*M) (Z+M)
lemma panorama (h:Time.Same P p): T= wave t z P := by unfold wave Rotunda.priceP; rw [h.1,h.2.1]
noncomputable abbrev room_charge (W:ℝ→ℝ) := wave t z P * district G L ζ t r z P J * (W t)^w * Real.exp ((P.supportExponent+8)* Trio.coverTicket z)
lemma eats (W:ℝ→ℝ) (ht:Geo G L W)(hd:0≤ ζ) (hx: ζ<s): ∀ᶠ i in atTop, room_charge G L ζ i r z w P J W ≤ tone G L i s r:= by
 have he := ((((floe G L z P).rate.mul (finial G L ζ r z P J hd)).mul (ht.power w).rate).mul_right (Real.exp ((P.supportExponent+8)*Trio.coverTicket z))); exact (he _ (show 0+(platform ζ r)+0 < platform s r from by simpa [platform])).mono fun t ht=>(le_abs_self _).trans ht
end Skull
end YM.Qlocal.Squall
