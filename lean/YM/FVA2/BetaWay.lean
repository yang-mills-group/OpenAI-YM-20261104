import YM.FVA2.Montage
import Mathlib.RingTheory.PowerSeries.Derivative
/-!
# Formal coupling scale law and conjugation, including genuine real-parameter jet derivative.
Uses f*g _point_ `ren a b` (b∘a). Below SP is real formal power series, flat ℂ if needed. No analytic claim about differentiated λ lift.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 540000
namespace YM.FVA2.Forge
open Function Filter Set Finset Pert Pert.Position Lattice Maxwell Maxwell.Free Pert.RawLabels PositionX PositionX.Jet PositionX.Ribbon PositionX.Detector PositionX.Bend Elegant PayAll Verne Panel Strat ColorCode Ember Legacy Taper
open MS MS.Plane MS.Land MS.Landau MS.Rake MS.High MS.Menus MS.Theater MS.Logarithm MS.Tide MS.Book MS.Book.Program MS.Book.Convolve Clock
open Hop
open scoped Topology ContDiff Classical
variable {G:Gauge} {F:Labels.Frames G} {r:ℝ}
namespace Meter
open PowerSeries
abbrev SP := PowerSeries ℝ
abbrev PS (v:Word ℝ): SP:= PowerSeries.mk v
variable (t:ℝ) (u:Word ℝ) (i p j:ℕ)
lemma ren_ps (v:Word ℝ)(h:light u): ren u v i=∑ p∈Finset.range (i+1), coeff i (PS u ^ p) * v p:= by
   obtain he:= Elegant.renReal v h i;
   have hc : Elegant.symbol u = PowerSeries.map Complex.ofRealHom (PS u):= by apply PowerSeries.ext; intro j; rw [Elegant.bill_q,coeff_map,PS,coeff_mk ]; rfl -- simp
   apply Complex.ofReal_injective; rw [he, Complex.ofReal_sum]; unfold Program.cut; simp_rw [hc, ← map_pow,coeff_map,Complex.ofReal_mul ]; rfl
-- derivative at outer coefficient. no arbitrary S.Top
lemma outer {u:ℝ→Word ℝ}{f:Word ℝ}(w:Word ℝ)(hw:light w)(h:∀ k,HasDerivAt (fun s=>u s k) ( f k ) t): HasDerivAt (fun s=> ren w ( u s ) i) (ren w f i) t:= by
   simp_rw [ ren_ps w _ _ hw ]; exact HasDerivAt.fun_sum (fun j _=> HasDerivAt.const_mul _ (h j)) -- binder implicit sum.M
-- differentiating powers of PS(headway + βt...). done without topology on PS.
lemma title (v:Word ℝ)(f:ℝ→Word ℝ)(p:ℕ)(i:ℕ) (hf:∀ i,HasDerivAt (fun s=>f s i) ( v i ) t): HasDerivAt (fun s=> coeff i (PS (f s) ^ p)) ((p:ℝ) * coeff i (( PS ( f t ) ) ^ (p-1) * PS v )) t:= by
    let X(s):= PS ( f s ); let V:= X t; let A:= PS v; induction p generalizing i with
    | zero=> simp_rw [pow_zero, Nat.cast_zero, zero_mul ]; exact hasDerivAt_const t _
    | succ p ih=>
      have hu (k j): HasDerivAt (fun s=>coeff k (X s ^ p)* coeff j ( X s )) ((p:ℝ) * coeff k (V^(p-1)*A)*coeff j V+coeff k (V^p) * v j) t := by
          simp_rw [show ∀ s, coeff j (X s)= f s j from fun s=> coeff_mk .. ]; -- mixed V RHS bound? X t defin
          rw [show coeff j V=f t j from coeff_mk ..]; exact (ih k).mul (hf j)
      simp_rw [pow_succ, coeff_mul (n:=i) (φ:=PS (f _) ^ p)]; -- `n=i` argument names.
      have hA:= HasDerivAt.fun_sum (u:=Finset.HasAntidiagonal.antidiagonal i) (fun j (_:j∈antidiagonal i)=> hu j.1 j.2); convert! hA using 1; -- match
      push_cast; rw [Finset.sum_add_distrib]; simp_rw [mul_assoc (p:ℝ), ← Finset.mul_sum, ← coeff_mul,show ∀ j,v j=coeff j A from fun _=>Eq.symm ( coeff_mk .. ), ← coeff_mul]; rw [ add_mul, one_mul, show (V ^ p) * A= (PS ( f t )) ^ p * PS v from rfl ]; congr 1
      cases p with| zero=> simp| succ p=> rw [Nat.add_one_sub_one,mul_right_comm,← pow_succ]
-- direct proof derivative at unit head. `PS.head`.
lemma head : PS headway= PowerSeries.X:= by
   apply PowerSeries.ext; intro n; rw [PS, coeff_mk, coeff_X ]; by_cases he:n=1; · rw [he,tip_head,if_pos rfl ]
   unfold headway someJ; rw [iteratedDeriv_id ]; by_cases hv:n=0 <;> simp [ he,hv] -- inspect

lemma ζ (w v:Word ℝ)(i:ℕ)(hw:light w) : ∑ p∈Finset.range (i+1),((p:ℝ)*coeff i ((PowerSeries.X:SP)^(p-1)*PS w))*v p= coeff i (derivative ℝ (PS v)*PS w):= by
    rw [ coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f:=fun a b=> coeff a (derivative ℝ _)*coeff b (PS w)), Finset.sum_range_succ', Finset.sum_range_succ ]; -- last rw select RHS
    simp_rw [ coeff_derivative ]; -- now
    simp only [Nat.cast_zero, zero_mul,add_zero,Nat.add_one_sub_one,Nat.cast_add,Nat.cast_one, Nat.sub_self,PS, PowerSeries.coeff_mk, show w 0=0 from hw,mul_zero ];-- likely order of `sum_range_succ'.L first` interfering
    refine Finset.sum_congr rfl fun j hj=>?_ ; have ht:= Finset.mem_range.mp hj; rw [ coeff_X_pow_mul', if_pos (by omega), coeff_mk ]; ring
lemma inner {g:ℝ→Word ℝ}{w:Word ℝ}(v:Word ℝ)(hw:light w) (hg:g t=headway)(h:∀s,light (g s))(hv:∀ i,HasDerivAt (fun s=>g s i) ( w i ) t): HasDerivAt (fun s=> ren (g s) v i) ( coeff i ( PowerSeries.derivative ℝ (PS v)*PS w )) t:= by
    simp_rw [ ren_ps _ _ _ (h _) ]; simp_rw [← ζ w v _ hw, ← Meter.head, ← hg ]; exact HasDerivAt.fun_sum (fun j _=> ( title t w g j i hv ).mul_const _)
end Meter
namespace Month
open Meter
variable {W:ℝ→ Hop F}{A:Panel F}{D:(d:ℕ)→ Detector F d}{R:Booth r F}(H:Month A W D R)
variable (t:ℝ)
def β (W:ℝ→Hop F)(i:ℕ) :ℝ:= deriv (fun t=> ( Month.ψ W t ) i) 0
include H
lemma headB (i:ℕ): HasDerivAt (fun t:ℝ=>Month.ψ W t i) (β W i) 0:= (( H.freshS.2 i ).differentiable (by simp) _ ).hasDerivAt
lemma zeroβ : β W 0=0∧ β W 1=0:= by
    constructor <;> unfold β; · rw [show (fun t:ℝ=>Month.ψ W t 0)=(fun _=>0) from funext fun t=> ( W t ).rooted ]; simp
    rw [show (fun t:ℝ=>Month.ψ W t 1)=(fun _=>1) from funext fun t=> ( W t ).primary ]; simp
lemma beta_path (i:ℕ): HasDerivAt (fun t:ℝ=> Month.ψ W t i) ( ren ( Month.ψ W t ) (β W) i ) t:= by
    have hp(s:ℝ):Month.ψ W s i= ren ( Month.ψ W t ) ( Month.ψ W (s-t) ) i := Eq.trans ( by rw [add_sub_cancel] : Month.ψ W s i= Month.ψ W (t+(s-t)) i) (congr_fun ( H.compositionψ t (s-t) ) _ );
    rw [funext hp ]; refine Meter.outer t i ( w:=_) ( W t ).rooted ( fun k=>?_ ); -- params
    have H':HasDerivAt (fun y:ℝ=>Month.ψ W y k) (β W k) (t-t):= by rw [sub_self]; exact H.headB _
    convert! H'.comp t (h:=fun y:ℝ=>y-t) ((hasDerivAt_id t).sub_const t ) using 1; simp
end Month
-- maps ∆ real & transported formal beta. PS usual.
open Meter
open Month (β ψ)
variable (V : Warehouse G) {O:Booked (wings G)}{q:ℝ}(h:G.Simple)(M:MS_Data G O)(T:Booth q V.F)(v:ℝ)(Sx: Pic.pass V h M T)
local notation "Fv"=> V.F
local notation "θ"=> nested V.F h (BoxOffice.warehouse V)
local notation "U"=> Forge.Mray V h M T v Sx
local notation "U₁"=> Forge.Cray V h M T v Sx
local notation "X0"=> Forge.Xray V h M T v Sx
lemma β_law : let f:= (Forge.transfer V M T v Sx).f; PS (Jet.ren f ( Month.β U ))= PowerSeries.derivative ℝ (PS f) * PS ( Month.β X0 ):= by
    intro f; apply PowerSeries.ext; intro n; rw [PS,PowerSeries.coeff_mk ]; obtain ht : (fun t:ℝ=> ren f (ψ U t) n)=(fun t:ℝ=> ren (ψ X0 t) f n):= by
       funext t; obtain hx:= Forge.scales_equate V h M T v t Sx; -- arguments order from variables.
       obtain hp:= congr_arg Hop.f hx; rw [ walkF, walkF, ψ_σ ] at hp; exact congr_fun hp.symm _
    obtain t₂:= Forge.real_X V h M T v Sx; let g:=ψ X0;
    refine HasDerivAt.unique (f:=fun t:ℝ=> ren (ψ X0 t) f n) ?_ (Meter.inner 0 n f t₂.zeroβ.1 t₂.tentative₀.1 (fun s=>( X0 s ).rooted) t₂.headB ); rw [ ← ht ]; exact Meter.outer 0 n f ( transfer V M T v Sx ).rooted ( Forge.real_ms V h M T v Sx|>.headB )
end YM.FVA2.Forge
