import YM.QuadraticLocal.Poetry.Glass
import YM.QuadraticLocal.Poetry.Knot
import YM.QuadraticLocal.Poetry.Bear
/-!
# Abelian height subtraction near every primary anchor
Uniform torus bound in lifted coordinates independent of ALL images.MarkAlias.
 Only an iteration step in converting the leading not-yet-matched analytic vertex.
 No decomposition of heights assumed on true periodic flat.Link, only polynomial limits via Athena.KNOT.
 Adapt local transfer lemma on `size(lift wrap)` from `RG02.Pinned.Fields`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry.Knot
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ker AllOrder.Ker.Start
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Field AllOrder.Ink.Money GaussianScore Module Push
open Sunrise Sunrise.Focus Haiku Stationary Pointwise Further.PhysicalPeriodLimitF933 Shingle Macrame
open Pinned Exterior
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n m:Side}{a C D b:ℝ}{k:ℕ}
variable {V α M:Type}[Fintype α][Fintype M][DecidableEq M] (T:Finset M)(q:M)
local notation "J"=> Coarse G⊕M
local notation "Ω"=> Point (Coarse G⊕M)
local notation "U"=>rule (Coarse G⊕M) n
variable (F:AllOrder.Ink.Field (Coarse G⊕M)) (A: Stationary.Link G n)(v:rule M n) (x:Site n) (s:Cover→ G.Color)

set_option quotPrecheck false
local notation "τ"=> Echo.amplify n
local notation "W" i:max => Ink.Echo.arm n i
local notation "U₀" => sendLink x A
local notation "z" i:max=> configure x (W i)
local notation "Y" j:max=> mingle ((convey (W j) A)-gradientA G (τ j) (poem (z j) s)) (convey (W j) v)
open Picket
lemma addon (k:ℕ)(c:ℝ)(h:0<c)(hp:0<a) : ∃ C>(0:ℝ),∀ x:ℕ,(c*(1+x:ℝ))^k ≤ C*Real.exp (a*x):= by
 let δ:= a/(k+1:ℕ); have hd : 0<δ:= div_pos hp (by positivity); let U₁:= δ⁻¹; have h₁: 0 < U₁:= inv_pos.mpr hd; refine ⟨(c+c/δ)^k,by positivity,fun i=>?_⟩; let α:ℝ:=i; have hi:0≤α:=Nat.cast_nonneg _; let T:= Real.exp (δ*α); have ht : 1≤T:=Real.one_le_exp (mul_nonneg hd.le hi); have h₂ : δ*α ≤ T:= by have hh :δ*α+1≤ T:= Real.add_one_le_exp _; linarith; -- scopes
 have hh: c*(1+α) ≤ (c+c/δ)*T:=by
      calc _ = c+(c/δ)*(δ*α):=by field_simp
           _ ≤ _:= (add_le_add (le_mul_of_one_le_right h.le ht) (mul_le_mul_of_nonneg_left h₂ (by positivity))).trans_eq (add_mul ..).symm
 have hL : T^k≤ Real.exp (a*i):= by rw [←Real.exp_nat_mul]; refine Real.exp_monotone (by rw [←mul_assoc]; gcongr ?_ * _ ; refine (mul_le_mul_of_nonneg_right (show (k:ℝ)≤(k+1:ℕ) from Nat.cast_le.mpr (Nat.le_succ k)) hd.le).trans_eq ?_; rw [mul_comm]; exact div_mul_cancel₀ _ (by positivity)) -- test
 rw [show c*(1+(i:ℝ))=_ from (show c*(1+(i:ℝ))= c*(1+α) from rfl)]; exact (pow_le_pow_left₀ (by positivity) hh k).trans ((mul_pow ..).le.trans (mul_le_mul_of_nonneg_left hL (by positivity)))
-- relative microscope.J.A.F fee*escort growth yields actual t.Lens threshold. No summing primary positions/hull:
lemma fare (p:Point α→ℝ)(x:Slip (Point α)) (h:∀ i∈x, ‖p i‖≤ b): ‖paid p x‖ ≤ b^x.length := by
   induction x with
   | nil=> simp [paid]
   | cons i x ih=> change ‖p i*paid p x‖≤_; have hp:=h i List.mem_cons_self; rw [norm_mul,List.length_cons,pow_succ']; exact mul_le_mul hp (ih fun i hi=>h i (List.mem_cons_of_mem _ hi)) (norm_nonneg _) ((norm_nonneg _).trans hp)
variable (hC:0≤C)(hs:∀ p:Cover,‖s p‖≤C*size p)(hp:0<a)(h:F.Good a b k)
local notation "Λ"=>F.fee
local notation "𝕏" i=> meter (F.slip i)
local notation "ν"=> page A v x s
include hp h
-- standalone utility for arbitrary.Z.Money rung.
lemma dollar (C:ℝ)(hξ:1≤C): ∃ B>(0:ℝ),∀ p:Point (Coarse G⊕M)→ℝ,(∀ i, ‖p i‖≤ C*(1+size i.1:ℝ)) → ∀ i:F.Ty, ‖(Λ i)*paid p (F.slip i)‖ ≤ B* F.price a i := by
 let hc:0<C:=lt_of_lt_of_le zero_lt_one hξ; obtain ⟨B,hB,h'⟩:= addon k C hc hp; refine ⟨B,hB,fun v hH i=>?_⟩ -- shadow h
 -- adjust bind
 let L:=F.slip i; have hv := fare v L (b:=C*(1+ (𝕏 i:ℕ):ℝ)) (fun s hs=> (hH s).trans (mul_le_mul_of_nonneg_left (add_le_add_right (Nat.cast_le.mpr (Picket.pending _ _ hs)) _) hc.le)); rw [norm_mul]; let d':ℝ:=1+meter L; have HD:1≤d':= le_add_of_nonneg_right (by unfold L; positivity); have hm:= (hv.trans (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hξ HD) (‹F.Good a b k›.length i))).trans (h' _); exact (mul_le_mul_of_nonneg_left hm (norm_nonneg _)).trans_eq (by unfold Field.price; rw [mul_comm _ (_*_ :ℝ),mul_assoc]; rfl) -- precision.hv braces
include hC hs
lemma point_limit : Tendsto (fun j=> F.site (τ j) (z j) (Y j)) atTop (𝓝 (∑' i:F.Ty,Λ i*paid (cycles A v x s) (F.slip i))) := by
 obtain ⟨a',ha,hA⟩:= size_fee A v x s hC hs; obtain ⟨Q,hQ,H⟩:= dollar F hp h a' ha
 let g(j:ℕ)(i:F.Ty) := Λ i*paid ((ν) j) (F.slip i); let G' (i:F.Ty):= Q* F.price a i; have hf : Tendsto (fun j=>∑' i:F.Ty,g j i) atTop (𝓝 (∑' i:F.Ty,Λ i*paid (cycles A v x s) (F.slip i))):= by
    refine tendsto_tsum_of_dominated_convergence (bound:=G') ((h.pay.2.1).mul_left Q) (fun i=>?_ ) (Eventually.of_forall fun j i=> H ((ν) j) (fun p=>hA p j) i)
    let S(p:Slip Ω): Prop:= ∀ᶠ j:ℕ in atTop, paid ((ν) j) p=paid (cycles A v x s) p; have hx (p:Slip Ω): S p:= by
       induction p with
       | nil=> exact Eventually.of_forall fun _=>rfl
       | cons p L ih=> exact ((trend A v x s p).and ih).mono (fun _ e=> congr_arg₂ (·*·) e.1 e.2)
    exact tendsto_const_nhds.congr' ((hx (F.slip i)).mono fun j he=> congr_arg (Λ i* ·) he.symm)
 exact hf.congr fun i=> tsum_congr (fun j=> congr_arg (Λ j*·) (show paid _ (F.slip j)= AllOrder.Ink.invoice (z i) (F.slip j) (Y i) from (by simp [AllOrder.Ink.invoice,paid,Function.comp_def]; rfl)))
omit hC hs
variable (ht:Fixed T q F)(hm:∀ (n:Side)(u: Stationary.Link G n)(v:rule M n)(p:BaseSites G n),F.table n (mingle u v)=F.table n (mingle (u-gradientA G n p) v))
include ht hm hs hC in
lemma ticket : F.site n x (mingle A v)= ∑' i:F.Ty,F.fee i*paid (cycles A v x s) (F.slip i):=by
 let g (i:ℕ):= F.site (τ i) (z i) (Y i); apply tendsto_nhds_unique _ (point_limit F A v x s hC hs hp h);
 refine tendsto_const_nhds.congr (fun i=> ?_); have he : F.site n x (mingle A v)=F.site (τ i) (z i) (mingle (convey (W i) A) (convey (W i) v)):= by
    rw [←AllOrder.Haiku.Glass.jumped n v (W i) A]; unfold Field.site; exact tsum_congr (fun j=> congr_arg (Λ j*·) (show invoice _ _ _= _ from ((by rw [Echo.voice,exactly] : invoice (z i) (F.slip j) _= invoice x (F.slip j) _).symm)))
 rw [he,← Picket.Fixed.receipt _ _ _ ht, hm, Picket.Fixed.receipt _ _ _ ht]
end YM.QuadraticLocal.Poetry.Knot
