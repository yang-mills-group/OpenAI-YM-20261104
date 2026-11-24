import YM.QuadraticLocal.Aperture.Bunch
import YM.QuadraticLocal.Poetry.Fish
/-!
 # The different issue of real rendering of the analytical answer for marked Taylor comparison
 Earnings.H plume supplies kernel identities (Art.Tool); they don't prove estimates on numerical
 Taylor Γ.Tx.S.PinCreative beam clocks, and can't hide an exponential-in-length.Ph.Pr. Here first
 deal with period wrapping/address matching. All labels retain whole crew list, never drop duplicate
 EXP-coupling.Slot. Only read filters at chart.Offset.Person.Creat.H
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Echo
open Function Filter Lattice Laurent Wilson RG Pressure Input Precision Tree Exterior
open Matrix Finset Push Uniform
open AbsoluteSums AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open Sunrise Sunrise.Focus Stationary
open MeasureTheory AllOrder.Floe
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
open Aperture Poetry
variable {ι V : Type}[Fintype V][DecidableEq V]{G:Gauge}{n:Side} (X: Lantern G V)(q:V)(W:V→ Site n)(L : Roll G V)
variable {k j e d:ℕ}
variable (hx:X.Bears Finset.univ q k) {a b C:ℝ}
namespace Spot
open Picket
local notation "Pt"=> Bunch.mapC W
def Entails : Prop:= ∀ p∈ X.roots, W p.2=W q + wrap n p.1
lemma pixels (i:Site n)(s:List (Point V)): invoice i s (Pt)= if (∀ p∈s,W p.2=i+wrap n p.1) then 1 else 0:= by
 induction s with
 | nil=> simp [Ink.invoice, Ink.paid]
 | cons x s ih=>
    let h : Prop:= ∀ p∈s,W p.2=i+wrap n p.1 -- better rw with ih abbrev
    change (if i+wrap n x.1=W x.2 then (1:ℝ) else 0)* Ink.invoice i s Pt = _; rw [show Ink.invoice i s (Pt) = if h then 1 else 0 from ih]
    have hh : (∀ p∈ (x::s), W p.2=i+wrap n p.1) ↔ (i+wrap n x.1=W x.2∧ h) := by
       simp only [List.forall_mem_cons, eq_comm (a:=W x.2)]; rfl
    simp only [hh]; by_cases ht:i+wrap n x.1=W x.2 <;> by_cases h':h <;> simp only [ht,h', and_self, and_true, false_and,and_false, ↓reduceIte, one_mul,zero_mul]

include hx
lemma origin_key {i:Site n} : (∀ p∈X.roots, W p.2=i+wrap n p.1) ↔ i=W q ∧ Entails X q W := by
 constructor; · intro H₀; have h:i=W q:=((H₀ _ hx.owns).trans (by simp)).symm; refine ⟨h,fun i hi=>?_⟩; rw [← h]; exact H₀ i hi -- only lhs simplified
 rintro ⟨η,h⟩; rw [η]; exact h
-- strip one leg. helps with later true Support audits.
lemma owns (b:V) : ∃ p:Cover,(p,b) ∈ X.roots:=by
 have ht:= (hx.considered b).trans (if_pos (mem_univ _)); obtain ⟨i,hi⟩:= (Picket.counts b _).1 (show 0<tally _ b from ht.symm ▸ (by omega : 0<1))
 obtain ⟨⟨s,s'⟩,hh,h⟩:= List.mem_map.mp hi; have h: s'=b := Sum.inr_injective (congr_arg Prod.snd h); exact ⟨s,h ▸ hh⟩
lemma chosen (i:Site n)(x:Link G n) : Lantern.gleam X i (Pt) e d x= if Entails X q W ∧ i=W q ∧ e≤d then Radial.jet (Helmet.frame X.atom (W q)) (d-e+X.r) x else 0:= by
 by_cases h:e≤d; swap; · rw [Lantern.pre X _ _ _ (by omega : d<e),if_neg (fun hx=> h hx.2.2)]; rfl
 rw [Lantern.placed _ _ _ _ _ _ h,pixels W]; by_cases ht:i=W q;
 · subst i; simp [Entails, h, mul_ite];
 rw [if_neg (fun p=> ht ((origin_key _ _ _ hx).mp p).1),if_neg (fun he=> ht he.2.1),mul_zero]
-- price: free tag.N.L. additional addresses can be eaten with remaining fraction.
omit hx
lemma monitor (a:ℝ)(ha:0≤a): X.atom.budget a ≤ X.money a := by
 unfold Atom.budget Lantern.money; apply mul_le_mul_of_nonneg_left _ (Texture.mag_nonneg _); unfold Lantern.length; gcongr; omega
variable (hL: L.Faith (Finset.univ:Finset V) q k a C)
local notation "X'" i=> L.leg i
local notation "Γ"=> L.price a
include hL
lemma wind_spread (ha:0 ≤ a)(se:Finset L.Ty) : ∑ i∈se,(L.leg i).atom.budget a ≤ C:= (Finset.sum_le_sum (s:=se) (g:=Γ) fun i _=> monitor (L.leg i) _ ha).trans (budget_sum hL.price se)
-- evaluation, single analytic coefficients.Agenda. Amp in bit filters. Operator Auth condition not hidden.
def label (a d:ℕ)(x:Link G n)(i:L.Ty):ℝ:= if Entails (L.leg i) q W ∧ a≤d then Radial.jet (Helmet.frame (L.leg i).atom (W q)) (d-a+(L.leg i).r) x else 0
local notation "V₀"=> label q W L
lemma anthem (e d:ℕ)(x:Link G n): (∑ a:Site n,∑' i, Lantern.gleam (L.leg i) a (Bunch.mapC W) e d x)= ∑' i,label q W L e d x i:=by
 simp_rw [show ∀ (i:L.Ty) (a:Site n), Lantern.gleam (L.leg i) a (Pt) e d x= _ from fun i a=> chosen (L.leg i) q W (hL.pinned i) a x]
 rw [Finset.sum_eq_single_of_mem (W q) (mem_univ _)]; · apply tsum_congr; intro i; unfold label; simp;
 intro b hb H; simp [H]
-- price of ALL lantern patches contains weight meters up to caller. later occupancy global.Payment.
end Spot
end YM.QuadraticLocal.Echo
