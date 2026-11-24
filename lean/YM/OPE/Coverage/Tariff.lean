import YM.OPE.Coverage.Downlength
import YM.OPE.Coverage.DemandStress

/-! # Currency changes between true and measured scales

Sub-log powers in bought weak labels, with a polynomial (not subpower)
charge for the admitted spatial discrepancy relative to a target window. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Coverage
open Set Function Filter Extraction Climb Ward Table Org Maxwell Spec Next.UVStress Extra Real Pert
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open WeakScaling
variable {G : Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order}
variable {H:Final C F S}{D n n':ℕ}{μ:ℝ}{r:ℕ→ℝ}(p:Stored H r D n μ)(hμ:0<μ)
set_option quotPrecheck false
local notation "Τ"=>Bel C.book
local notation "U"=>p.maps
local notation "ρ"=>p.path

def Poly {X:Type*}[Norm X](r:ℕ→ℝ)(f:ℕ→X):Prop := ∃ b:ℝ,RateLE atTop (fare r) f b
variable {X Y:Type*}
lemma Poly.absBound [Norm X]{f:ℕ→X}(he:Fine r){A:ℝ}(h:∀ᶠ i in atTop, ‖f i‖ ≤ A):Poly r f:=⟨0,RateLE.absBound A (fare_large r he) h⟩
variable {f:ℕ→X}
include p
lemma meter_comparable (he:Fine r): ∀ᶠ i in atTop, fare r i ≤ 2*fare p.path i ∧ fare p.path i ≤ 2*fare r i := by
   obtain ⟨c,hc,h'⟩:=p.window.2 -- wrong field
   have hQ :=p.fades.2; filter_upwards [he.2.eventually (log_speed _ hc),hQ.eventually_ge_atTop 2,he.2.eventually_ge_atTop 2,h'] with i hx hy hx' h
   let x:=mark r i;let y:=mark p.path i
   have h1:= hx.1.trans hx.2
   have h₂ : x ≤ 2*y := by have h':=le_trans (le_abs_self (x-y)) h; linarith only [h',h1]
   have h₃ : y ≤ 2*x := by linarith only [neg_le_of_abs_le h,h1,hx']
   have hmon(x y:ℝ) (hx: 2≤x)(hy:2≤y)(h:x≤2*y): log (1+x) ≤ 2*log (1+y):=by
      rw [two_mul,← Real.log_mul (by linarith only [hy]) (by linarith only [hy])]; exact log_le_log (by linarith only [hx]) (by nlinarith only [sq_nonneg y,h])
   exact ⟨hmon x y hx' hy h₂,hmon y x hy hx' h₃⟩
lemma Poly.keeping [NormedAddCommGroup X] (he:Fine r) (hf:Poly ρ f):Poly r f:=by
   obtain ⟨b,hb⟩:=hf
   refine ⟨2*max b 0,fun a ha=>?_⟩
   filter_upwards [hb (a/2) (by linarith only [le_max_left b 0,ha]),meter_comparable p he] with i hi hx using hi.trans (Real.exp_monotone (by change a/2*fare ρ i ≤ a*fare r i; nlinarith only [hx.2,ha,le_max_right b 0]))
omit p
lemma Poly.add [SeminormedAddGroup X]{g:ℕ→X}(hr:Fine r)(h:Poly r f)(hg:Poly r g): Poly r (fun i=>f i+g i):=⟨_,h.choose_spec.addMax hg.choose_spec (fare_large r hr)⟩
lemma Poly.congr [Norm X]{g:ℕ→X}(h:Poly r f)(hv:f=ᶠ[atTop]g): Poly r g:=⟨_,h.choose_spec.congr hv⟩
lemma Poly.smul [SeminormedAddCommGroup X]{𝕜 : Type*}[NontriviallyNormedField 𝕜][NormedSpace 𝕜 X] {g:ℕ→𝕜}(h:Poly r g)(hf:Poly r f):Poly r (fun i=>g i • f i):=⟨_,RateLE.smul h.choose_spec hf.choose_spec⟩
lemma Poly.pow [SeminormedRing X](k:ℕ)(h:Poly r f)(ht:Fine r): Poly r (fun i=> (f i)^k):=⟨_,RateLE.pow k h.choose_spec (fare_large r ht)⟩
lemma Poly.prod {ι : Type*} [Fintype ι] [SeminormedCommRing X]{x:ℕ→ι→X}(hr:Fine r)(h:∀ j:ι, Poly r (fun i=> x i j)) : Poly r (fun i=> ∏ j,x i j) :=⟨_,RateLE.prod (r:=fun j:ι=>(h j).choose) (f:=fun j i=>x i j) (fare_large r hr) fun j _=>(h j).choose_spec⟩
lemma Poly.sum {ι : Type*}[Fintype ι] [SeminormedAddCommGroup X]{x:ℕ→ι→X}(hr:Fine r)(h:∀ j:ι, Poly r (fun i=> x i j)) : Poly r (fun i=> ∑ j,x i j):=by
   choose c hc using h
   exact ⟨_, RateLE.sum (f:=fun i:ι=> fun j:ℕ=>x j i) (a:=∑ i, |c i|) (fare_large r hr) (fun i hi=>(hc i).mono (le_trans (le_abs_self _) (Finset.single_le_sum (fun i _=>abs_nonneg (c i)) hi)))⟩
lemma Poly.map [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] (h: Poly r f)(L:X →ₗ[ℂ] Y)(hr:Fine r) :Poly r (fun i=>L (f i)):=by
   let g:=L.toContinuousLinearMap
   refine ⟨(show ℝ from 0)+h.choose,RateLE.bil (RateLE.const ((‖g‖):ℝ) (fare_large r hr)) h.choose_spec (Eventually.of_forall fun i=>?_)⟩
   exact (g.le_opNorm _).trans_eq (by rw [norm_norm])

include p
local notation "f₀"=> mark r
lemma price_ratio(he:Fine r): ∃ b:ℝ, 0≤b ∧ ∀ᶠ i in atTop, r i / p.path i ≤ exp (b*fare r i):=by
   obtain ⟨_,c,hc,h⟩:=p.window
   refine ⟨c,hc.le,?_⟩
   filter_upwards [h] with i hi
   have hh:=le_trans (le_abs_self (-(mark r i - mark ρ i))) ((abs_neg ..).le.trans hi)
   refine le_trans ?_ (Real.exp_monotone hh)
   apply le_of_eq; change _ = Real.exp ( -(-Real.log (r i)-(-Real.log (ρ i))))
   rw [show -(-Real.log (r i)-(-Real.log (ρ i))) = Real.log (r i)- Real.log (ρ i) from (by ring), exp_sub,exp_log (he.1 i),exp_log (p.fades.1 i)] -- identity sign wrong neg_sub_neg; test
lemma ratio_le(he:Fine r): Poly r (fun i=>r i / p.path i):=by
      obtain ⟨b,_,hB⟩:=price_ratio p he
      exact ⟨b,(RateLE.exp b (fare_large r he)).of_norm_le (hB.mono fun i hi=> (Real.norm_of_nonneg ((div_pos (he.1 i) (p.fades.1 i)).le)).le.trans hi)⟩
open Next.UVStress
local notation "Λ" =>fun d:Fin n'→ℕ=>Ribbon (Bel C.book) d
include hμ
lemma airy_moving (t:Caps n') (v:ℕ→Ribbon (Bel C.book) t) (ht:Fine r)(hn:n'≤ n)(hD:∀ j,t j≤ D) (z:ℕ→Points n')(h:∀ j,Poly r (fun i=>v i j))(hz:∀ᶠ i in atTop, z i∈airy n' (p.path i/(2*μ))):Poly r (fun i=>disc (panels (p.maps i) ∘ hang t (v i)) (z i)):=by
   let g(x:record C t)(i:ℕ):= disc (panels (p.maps i) ∘ hang t (depthWord t x)) (z i)
   have hf(x:record C t): Poly r (g x):= (Poly.keeping p ht ⟨0,airy_spending H p t x hD hn hμ z (by simpa only [p.spot] using hz)⟩)
   let q(x:record C t)(i:ℕ):=coords _ x (v i)
   have hq x: Poly r (q x):=by
      exact Poly.prod (x:=fun i j=> (Module.finBasis ℂ _).repr _ (x j)) ht (fun j=> (h j).map ((Module.finBasis ℂ _).coord _) ht)
   have h:=Poly.sum (x:=fun i x=> q x i • g x i) ht (fun x=>(hq x).smul (hf x))
   refine h.congr (Eventually.of_forall fun i=>?_)
   let M(i:ℕ):= (S.classMoment S t (z i)).compLinearMap fun j=>p.maps i (t j)
   exact Eq.symm (basis_tuple _ (v i) (M i))
end YM.OPE.Coverage
