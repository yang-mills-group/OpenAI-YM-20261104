import YM.AllOrder.Ink.Slab
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ink
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
namespace Money
open Method GaussianScore
variable {V:Type} {Λ:V→ℝ}{f g:V→Bills α}{Ad:Side→Prop}
-- earned Lines for all λ in region. can then choose family per-Path h. σ fixed strip on optics even under thinning.
variable (A:V→Stalk α α){P:V→ℝ}(hP:Grade Λ P)(ht:0<a)(H:∀ v,Belt (A v) a (P v))
include H hP ht
lemma Apt.furnish (h:Apt Ad Λ f k): Apt Ad Λ (fun v n=> flicker (A v) n (f v n)) (k-2) := by
 obtain ⟨b,hb,H'⟩:= h; let x:= min a b; have hh:0<x:=lt_min ht hb; have hX v:= (H v).debt (min_le_left a b) le_rfl; obtain ⟨F,C,D,hC,hD,h⟩:= Apt.squeeze H' (min_le_right a b) (le_refl k)
 let w:= ((k*k:ℕ):ℝ); have hw : 0 ≤ w:= Nat.cast_nonneg _; let d(v:V)(n:Side):ℝ:=Fintype.card (Leaf n α); let u:=gia (Λ:=Λ) w hw; let hu:= u.mul (hP.mul hC)
 let Z v:= plan (F v) (funds (A v)); have hg v:= crux (A v) (F v) (h v).1 (hX v) hh.le (hP.nonneg v);
 let T₀(v:V)(n: Side):ℝ := Fintype.card (Site n) * (w*(P v*C v)); let D' := fun (v:V) (n: Side)=> d v n*(d v n*(P v*((D v n *honor k) * honor (k-1))))
 have hT: Pay Λ T₀:= (Pay.low Λ).times (Pay.lift hu); have h' : Pay Λ D':= Pay.times (Pay.grid α Λ) ((Pay.grid α Λ).times ((Pay.lift hP).times ((hD.times (Pay.fixed Λ _ (honor_pos k).le)).times (Pay.fixed Λ _ (honor_pos _).le))))
 refine ⟨x,hh,Z,_,_,hu,hT.stamp h',fun v=> ⟨hg v,fun n hn=>?_⟩⟩; let f':=f v n; let g':=(F v).table n; let X':=flicker (A v) n; let R:= dearth x n; have hx : Prices k (D v n* R) (f'-g'):= (h v).2 n hn; have hE:= prices_flick (A v) (hX v) (hP.nonneg _) hh.le hx; let Y:=(Z v).table n
 have hC: Prices (k-2) (T₀ v n * R) (X' g'-Y):= by
    unfold T₀; rw [mul_assoc (Fintype.card (Site n):ℝ), show w*(P v*C v)*R=w*((R*P v)*C v) from (by ring)]; exact carbon (H:= (h v).1) (hX v) hh.le (hP.nonneg _) _ -- arguments
 have hu: Prices (k-2) (D' v n * R) (X' (f'-g')):= by rw [show D' v n * R=d v n *(d v n*(P v*((D v n*R*honor k)*honor (k-1)))) from (by unfold D'; ring)]; exact hE
 change Prices (k-2) ((T₀ v n+D' v n)*R) (X' f'-Y); rw [add_mul, show X' f'-Y = (X' g'-Y)+ X' (f'-g') from ?_]; · exact price_add hC hu
 have hv := ((h v).1.binding (n:=n) hh.le).2.1.read; rw (occs:=.pos [1]) [← add_sub_cancel g' f', show X' (g'+ (f'-g'))=_ from (flicker_plus (A v) _ _ hv hx.2.1.read)]; abel
end Money
end YM.AllOrder.Ink
