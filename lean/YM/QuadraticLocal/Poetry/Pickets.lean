import YM.QuadraticLocal.Sunrise.Teapot
import YM.QuadraticLocal.Poetry.Vernal
import YM.AllOrder.Ink.Aisle
/-!
# Real anchored root projection on path stamps
 Shift *representation* by incidence location of a chosen input mark lens field.
 Not assuming any of those are already paid in Burn.Student path yet. Pay explicit root width. This
 is for analytic tape P, anchored to *same primary mark* when traveling from fine tree. Gauge
 consequences use independence of all lamp illumination profiles. In particular no tear across
 aliases.Ed. Pos selection even at rank zero (analytic scalar terms). Allows unmasked long terms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ker AllOrder.Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Field AllOrder.Ink.Money GaussianScore Module Push
open Sunrise Sunrise.Focus
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n m:Side}{a C D b:ℝ}{k:ℕ}
variable {V α M:Type}[Fintype α][Fintype M][DecidableEq M] (T:Finset M)(q:M)
local notation "J"=> α⊕M
local notation "Ω"=> Point (α⊕M)
local notation "U"=>rule J n
-- select mark occurrence from Depicted.H.N queries
namespace Picket
lemma counts (L:List (V×(α⊕M))) : 0 < tally L q ↔ ∃ i:V,(i,Sum.inr q)∈L:= by
 induction L with
 | nil=> simp [tally]
 | cons i L ih=>
    rw [stamped]; rcases i with ⟨v,i|i⟩; · simp [calls,ih]
    by_cases he:i=q; · subst i; simp [calls,Nat.add_comm];
    simp [calls,he, Ne.symm he,ih]
variable (hq:q∈T) (F:AllOrder.Ink.Field (α⊕M))(hp:∀ i,Depicted T (F.slip i))
def offset (i:F.Ty): Cover:= if h: ∃ x:Cover,(x,Sum.inr q)∈ F.slip i then h.choose else 0
def wheel : AllOrder.Ink.Field (α⊕M) := ⟨F.Ty,F.fee,fun i=> Field.along (- offset q F i) (F.slip i)⟩
local notation "Λ₀"=> wheel q F
local notation "pt" i:max=> offset q F i
lemma tally_s (L:Slip (Point (α⊕M)))(i:M)(x:Cover): tally (Field.along x L) i=tally L i:= by
 induction L with | nil=>rfl | cons y L ih=> change tally (Field.plus y x :: Field.along x L) i =_; rw [stamped,stamped,ih]; rfl -- `plus` ambiguous
include hq hp
lemma position (i:F.Ty): (pt i,Sum.inr q)∈F.slip i:= by have he:= (counts q (F.slip i)).mp (show 0<tally _ q from ((hp i q)).trans (if_pos hq) ▸ (by omega : 0<1)); unfold offset; rw [dif_pos he]; exact he.choose_spec -- declaration auto.K.Arg.T etc.
-- every anchored real.Fie candidate.T.Code
structure Fixed (T:Finset M)(q:M)(F:AllOrder.Ink.Field (α⊕M)) : Prop where
    tracked : ∀ i, Depicted T (F.slip i)
    root : ∀ i,(0,Sum.inr q)∈ F.slip i
lemma found : Fixed T q (wheel q F):= by
 constructor; · intro i x; exact (tally_s _ x _).trans (hp i x)
 intro i; unfold wheel Field.along; exact List.mem_map.mpr ⟨_,position T q hq F hp i, Prod.ext (neg_add_cancel _) rfl⟩
omit hp hq in
lemma pending (i:Ω)(L:Slip (Point (α⊕M)))(hi:i∈L): size i.1≤ meter L:= by -- omit HP
 induction L with
 | nil=> simp at hi
 | cons j L ih=> rcases List.mem_cons.mp hi with he|he; subst j; exact Nat.le_add_right ..; exact Nat.le_trans (ih he) (Nat.le_add_left ..)
variable (h:F.Good a C k)(hb:b*(k+1:ℕ)≤ a)(hx:0≤ b)
include h hb hx
lemma gears : (wheel q F).Good b C k:= by
    have h1 (i:F.Ty):meter ((wheel q F).slip i)≤ (k+1)*meter (F.slip i) := by
       have he:= position T q hq F hp i; have hh:= h.length i; let p:=meter (F.slip i); have ht:size (- offset q F i)≤p:= by rw [size_neg]; exact pending (offset q F i,Sum.inr q) _ he
       apply Nat.le_trans (Field.lifted_cost (F.slip i) (-offset q F i)); unfold p at ht; rw [add_mul,one_mul]; gcongr
    refine ⟨fun i=> by change List.length (Field.along _ _ ) ≤_; unfold Field.along; rw [List.length_map]; exact h.length i,sumBudget_mono h.pay ((Λ₀).price_nonneg b) (fun i=> ?_) le_rfl⟩; unfold Field.price; refine mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) (abs_nonneg _); refine (mul_le_mul_of_nonneg_left (show (↑(meter _):ℝ) ≤ ↑((k+1)*meter (F.slip i)) from Nat.cast_le.mpr (h1 i)) hx).trans ?_; rw [Nat.cast_mul,← mul_assoc]; exact mul_le_mul_of_nonneg_right hb (by positivity)
lemma echoes (n:Side)(x:rule (α⊕M) n): (Λ₀).table n x=F.table n x:= by
    let T₁:= Λ₀; have ht:= gears T q hq F hp h hb hx; have he : 0≤a:= (mul_nonneg hx (by positivity)).trans hb; let f(i:F.Ty)(z:Site n):= F.fee i*invoice z (F.slip i) x; rw [Field.table_apply, Field.table_apply]; unfold Field.site; rw [←Summable.tsum_finsetSum (fun z _=>ht.total hx z x), ←Summable.tsum_finsetSum (fun z _=> h.total he z x)]; change ∑' i:F.Ty, _= _; refine tsum_congr fun i=>?_ ; let L:=F.slip i; let V(x:Site n):= x+ wrap n (- offset q F i); change ∑ u: Site n,F.fee i*invoice u (Field.along _ L) x =_; simp_rw [Field.lifted]; exact Equiv.sum_comp (Equiv.addRight (wrap n (- offset q F i))) (f i)
end Picket
end YM.QuadraticLocal.Poetry
