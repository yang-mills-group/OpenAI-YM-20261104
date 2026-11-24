import YM.FVAAlt2.Rocket.Code
import YM.FVAAlt2.Shop.Match
/-! # Polynomially re-price the actual bare matrices
Rates through *specified finite order*, Meter can include any step costs
 at our stated schedule. This is **epsilon power growth**, not a logarithmic value result.
Using TIDE the weights & the entire fixed Knob solution will be bought prior
 to limit. Thus witness doesn't assume matrix remains bounded on thermal geometry.
Enough if log$L$ $∼O(age of finer ticks)^γ ≪ length to soft stop$.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Rocket
open Set Filter MeasureTheory Function Finset
open Binding Diagram.Formal Prim PowerSeries
open Lattice Gauge Geometry Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Epoch
open PertExtension Series Series.Radial Series.Tested Chart Orb
open YM.FVAAlt2
open Billing Labels Source
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {X I:Type}{P: X→ℝ≥0∞}{L: Meter X}{F:Type*} [NormedField F] {q:ℕ}
-- price operations
local notation "cPs"=> PowerSeries ℂ
lemma polyAdd {f g:X→ ℝ}(h:Poly L fun i=>‖f i‖ₑ)(hh:Poly L fun i=>‖g i‖ₑ) : Poly L fun i=>‖f i+g i‖ₑ:= (h.add hh).mono fun _=> enorm_add_le ..
lemma polySub {f g:X→ ℝ}(h:Poly L fun i=>‖f i‖ₑ)(hh:Poly L fun i=>‖g i‖ₑ) : Poly L fun i=>‖f i-g i‖ₑ:= (h.add hh).mono fun _=> enorm_sub_le ..
lemma polyMul {f g:X→ ℝ}(h:Poly L fun i=>‖f i‖ₑ)(hh:Poly L fun i=>‖g i‖ₑ) : Poly L fun i=>‖f i*g i‖ₑ:= (h.mul hh).mono fun _=> (enorm_mul ..).le
lemma powerLaw {f:X→ ℝ}(h:Poly L fun i=>‖f i‖ₑ)(d:ℕ):Poly L fun i=> ‖f i ^ d‖ₑ:= (h.powQ d).mono fun i=> (enorm_pow ..).le
lemma PPrice {f:X→ ℝ}(h:Poly L fun i=>‖f i‖ₑ)(Q:Polynomial ℝ) :Poly L fun i=> ‖Q.eval (f i)‖ₑ:=by
 induction Q using Polynomial.induction_on' with
 | add X Y i j=> simp_rw [Polynomial.eval_add]; exact polyAdd i j
 | monomial n a=> simp_rw [Polynomial.eval_monomial]; apply polyMul (f:=fun _=>a) (Poly.standard _ (by finiteness)); exact powerLaw h _
lemma complexView {f:X→ ℝ}(h:Poly L fun i=>‖f i‖ₑ): Poly L fun i=>‖Complex.ofReal (f i)‖ₑ:=by simpa [← ofReal_norm] using h
section PS
omit [NormedField F]
def Price (L:Meter X)(p:ℕ)(V:X→ cPs) := ∀ e≤p,Uniform.Poly L fun i=> ‖coeff e (V i)‖ₑ
variable {p:ℕ}{V U:X→ cPs}
lemma Price.one : Price L p (fun _=>1) := fun _ _=> Poly.standard _ (by finiteness)
lemma enormSum {E: Type} [NormedAddCommGroup E](s:Finset I)(F:I→E): ‖(∑ i∈s,F i)‖ₑ ≤ ∑ i∈s, ‖F i‖ₑ:= enorm_sum_le ..
lemma Price.mul (h:Price L p V)(hp:Price L p U): Price L p fun i=> V i*U i:=by
 intro i hi; simp_rw [coeff_mul]; let f(t: ℕ×ℕ) (v:X):= coeff t.1 (V v) * coeff t.2 (U v)
 refine (Poly.sum (antidiagonal i) (fun t v=> ‖f t v‖ₑ) (fun t ht=>?_)).mono fun _=> enormSum ..
 have ht:= mem_antidiagonal.mp ht; exact ((h t.1 (by omega)).mul (hp t.2 (by omega))).mono fun _=> (enorm_mul ..).le
lemma Price.pow (h:Price L p V)(n:ℕ): Price L p fun i=> V i ^ n:= by
 induction n with
 | zero=> simpa using (Price.one (L:=L) (p:=p))
 | succ i ih=>simp_rw [pow_succ]; exact ih.mul h
lemma Price.C' {v:X→ℂ}(h:Poly L fun i=> ‖v i‖ₑ): Price L p (fun i=>C (v i)):=by intro e he; rw [show (fun i=>‖coeff (R:=ℂ) e (C (v i))‖ₑ)=if e=0 then (fun i=>‖v i‖ₑ) else 0 from funext fun i=>by split_ifs with hx; simp [hx]; simp [PowerSeries.coeff_C,hx]]; split_ifs; exact h; exact Poly.zeroQ _
lemma Price.prod (s:Finset I)(v:I→X→cPs)(h:∀ i∈s,Price L p (v i)): Price L p (fun x=>∏ i∈s, v i x):=by
 induction s using Finset.induction_on with
 | empty=> simp only [Finset.prod_empty]; exact Price.one
 | insert i s hi ih=> simp_rw [Finset.prod_insert hi]; exact (h i (mem_insert_self ..)).mul (ih fun j hj=>h j (mem_insert_of_mem hj))
def Scored (L:Meter X)(P: X→ℝ≥0∞)(p:ℕ)(V:X→ cPs):= ∀ e≤p, Carry L P fun i=> ‖coeff e (V i)‖ₑ
lemma Scored.mul (h:Price L p V)(hp:Scored L P p U): Scored L P p fun i=> V i*U i:=by
 intro i hi; simp_rw [coeff_mul]; let f(t: ℕ×ℕ) (v:X):= coeff t.1 (V v) * coeff t.2 (U v)
 refine (Carry.sum (antidiagonal i) (fun t v=> ‖f t v‖ₑ) (fun t ht=>?_)).mono fun _=> enormSum ..
 have ht:= mem_antidiagonal.mp ht; exact (Carry.mul_left (h t.1 (by omega)) (hp t.2 (by omega))).mono fun _=> (enorm_mul ..).le
lemma Scored.sum (s:Finset I)(v:I→X→cPs)(h:∀ i∈s,Scored L P p (v i)): Scored L P p fun x=>∑ i∈s, v i x:=by
 intro e he; simp_rw [map_sum]; exact (Carry.sum s (fun j i=>‖coeff e (v j i)‖ₑ) (fun i hi=> h i hi e he)).mono (fun i=>enormSum ..)
open MS.Book.Program MS.Menus MS.Dial
variable {G:Gauge}{d: MS.Local.Physical.Deck G}(K: MS.Land.Prescription d){θ:X→ℝ}
lemma shiftFits (h: Poly L fun i=> ‖θ i‖ₑ): Price L p fun i=> MS.Book.Program.shift K.team (θ i):= by
 intro e _; unfold MS.Book.Program.shift; simp_rw [PowerSeries.coeff_mk]; split_ifs
 · exact Poly.standard _ (by finiteness)
 · exact Poly.standard _ (by finiteness)
 exact complexView (PPrice h _)
-- fund just before frame vs after other normalization. bore powers polynomial uniformly all native placements.
variable [LinearOrder I]
lemma chargeGlyph (h:Poly L fun i=> ‖θ i‖ₑ)(z:I→ MS.Rake.Label d)(x:I)(j:Glyph d (z x).h) :Price L p (fun y=> bore z K (θ y) x j):=by
 intro e _; unfold bore oil;simp_rw [coeff_mk];exact complexView (PPrice h _)
omit [LinearOrder I]
lemma Scored.reset {V:X→cPs}(h:Poly L fun i=> ‖θ i‖ₑ)(he:Scored L P p V): Scored L P p fun i=> Lobby.redo K.team (θ i) (V i):=by
 intro e hh
 unfold Lobby.redo; simp_rw [LinearMap.coe_mk, AddHom.coe_mk, coeff_mk,rules]; unfold cut; apply Carry.mono (g:=fun t=>∑ i∈Finset.Iic e,_) ?_ (fun _ =>enormSum ..); apply Carry.sum; intro i hi; have h':i≤e:= mem_Iic.mp hi;
 exact ((Carry.mul_left ( (shiftFits K h).pow i e hh ) (he i (h'.trans hh)) ).mono fun _=> (enorm_mul ..).le)
end PS
end YM.RegulatorIR.FVAAlt2.Rocket
