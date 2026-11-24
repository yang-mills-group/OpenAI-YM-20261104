import YM.Qlocal.Quipu.Era
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Eluder
open AllOrder AllOrder.Ink Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
open Turbin Sonnet Marker Kinetic Primitives.GCC.Anchor
variable {ι α :Type}[Fintype α][DecidableEq α] {G:Gauge} {n:Side} {k N :ℕ} {a b r :ℝ}{R:Marker.Census α}
open Ballad Dais Zora Lasso AnalyticNext.QuarticMatch Joint CubicMatch
open Album Exterior
namespace Incline
namespace Bookworm
open Macarons Tracks Tender Lagger Sonnet.Tern
local notation "S"=> Coarse G
local notation "Z"=> Coarse G ⊕α
local notation "Ω"=> rule (Coarse G) n
local notation "X"=> rule (Coarse G⊕α) n
local notation "E"=> fieldDir G n 1
variable {Ad:Side → Prop} {Γ:ι→ℝ}{m k0 r':ℕ}
local notation "I"=> ι
variable {P:ℕ→ι →Ink.Money.Bills ((Coarse G) ⊕α)} (T: Anthem ι α G N Γ a m Ad P)
namespace Anthem
variable (W:Noon G N) (O:Lattice.Order) (Y: α→ℕ) (t:ℕ) (h:∀ s:Senses R,warrant k s Y N) (ha:0<a)
variable {e g:ℕ} (s:Senses R)
local notation "τ[" s "," n "]"=> lap_s Y s n
local notation "τ0[" s "," n "]"=> lap Y s n
variable (x:ι)
local notation "S[" s "," e "]"=> T.tune (lap_s Y s e) x
set_option quotPrecheck false
local notation "H0[" s "," e "]"=> (charged (k:=k) s Y (h s) (Nat.le_of_lt_succ (Fin.isLt e)))
variable (U:ℝ) (hU:0<U) (hx:U*(5*N:ℝ) ≤ a/2)
local notation "F[" n "," t "]"=> Fin (lap Y n t+1)
variable (j:Fin (k+1)) (o:α→Site n) (v:rule (Coarse G) n)
local notation "C"=> ports G n
set_option quotPrecheck false
local notation "V"=> layout T W O Y t h x
local notation "P0"=> datum T W O Y t h s x o
variable (hn: Ad n) (he:e≤k) (ht: N ≤ t)
local notation "τ"=> lap_s Y s (Fin.val j)
local notation "q0"=> lap Y s (Fin.val j)
local notation "k'"=> (lap Y s (Fin.val j)) -- uncaptured macro avoid. compiler
local notation "Q"=> Tender.crystal R s.val o
local notation "X'"=> (lap_s Y s (Fin.val j)-(essence s).card)
local notation "P'"=> (P (lap_s Y s (Fin.val j)) x n)
local notation "Y'"=> T.tune τ x
local notation "Θ"=> verse (P:=P) Y s x o
local notation "B0"=> T.fund τ x n
local notation "C'"=> T.d τ x
local notation "D"=> (dearth a n)
local notation "ι'"=> s.val.val.card
local notation "H'"=> (T.tune (lap_s Y s (Fin.val j)) x).typeR.table n
local notation "c0"=> Tender.inst (s.val.val.card) (lap_s Y s (Fin.val j))
local notation "d0"=> ((B0)*D* c0)
variable (hv:‖v‖≤1) (hh:PaintSupply G (t+1) b) (hp:Allows (t+1) G.plog 1 r)
local notation "μ"=> overF (P:=P) W O Y s x o v
local notation "Kκ"=> (growth (b:=b) (r:=r) (n:=n) T W Y t s x (Fin.val j))
local notation "ξ"=> (down₁ T W Y t n U b r s x (Fin.val j))
-- charge hwt Scope. sample truth.S. immutable St.Art before. α_Sigma E.Weight.Gr.Scope K.Height decisions.Th.Commitment 
include T hp hh h ht hU
local notation "m₀"=> ((t+1)*(t+1))
def rankC (t:ℕ):ℕ:= (t+1)*(t+1)*t+(t+1)*(t+1)*t
local notation "kβ"=> rankC t
lemma nameβ : Weight Γ kβ (fun (_:ι) n=> Tracks.pawnout t (lap Y s j) (leaning G n (t+1) b r)):= by
 have he:lap Y s j≤t:= ( (Nat.le_add_right ..).trans ((show lap_s Y s j ≤ N from H0[s,j]).trans ht)); apply (Tracks.quote Γ t (lap Y s j) (prosperity hh hp Γ)).ups; -- order inspect
 unfold rankC; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ he) _
lemma laneβ : Weight Γ (m+kβ) (fun x n=> down₁ T W Y t n U b r s x j.val):= by
 -- no lag losses.L.Ok
 let v:= τ; have hs:Weight Γ kβ (fun _ n=>mount (lap_s Y s j.val) (lap Y s j.val) t W n b r U a):= by
    simp only [mount]
    have hc:0≤rentS W:=by unfold rentS; positivity
    simpa only [Nat.zero_add,Nat.add_zero] using! (Weight.times (((Weight.fixed Γ _ (freight_ok W t U hU hh (lap Y s j) (k:=lap_s Y s j))).ups (Nat.zero_le (0+kβ))).stamp ((Weight.fixed Γ _ hc).times ( nameβ T Y t h s U hU j ht hh hp))) (Weight.fixed Γ _ (Real.exp_pos (a/2)).le))
 let u:= T.pays v H0[s,j]; have hk:= Weight.times hs (Weight.lift u.1); have hp':0 ≤ rentS W*Tender.inst s.val.val.card τ:= by have he:= Tender.valid s.val.val.card τ; unfold rentS; positivity; 
 have hQ : Weight Γ (m+kβ) (fun i n=> growth (b:=b) (r:=r) (n:=n) T W Y t s i j.val):= by simpa only [Nat.zero_add] using! ( (Weight.times (Weight.fixed _ _ hp') u.2).times ( nameβ T Y t h s U hU j ht hh hp))
 exact Weight.stamp (Weight.ups hk (show kβ+m≤ m+kβ from Nat.add_comm ..|>.le)) hQ
noncomputable abbrev topWeight (k:ℕ) (e:ℕ) (n:Side):= Tracks.foster (lap Y s e) * (∑ j:Fin (k+1),down₁ T W Y t n U b r s x j.val)
lemma payment (e:ℕ) : Weight Γ (m+kβ) (fun i n=> topWeight (b:=b) (r:=r) T W Y t s i U k e n):= by
 simpa only [Nat.zero_add] using! (Weight.times (Weight.fixed Γ _ (Tracks.foster_ge (lap Y s e)).le) (Weight.sum (univ:Finset (Fin (k+1))) (fun i _=> T.laneβ W Y t h s U hU i ht hh hp)))
omit hp hh ht hU
-- Desire true transport of Wood.L.Ph. not requiring any arbitrary desired smallness. Actual Fk.L κ gives this EXACT. Pose.SeE.
open Comparison.RG02.Symmetry (glows)
open Comparison.RG02.Symmetry.Orbit (Sheet patrol)
variable (Φ:ℕ→fieldDir G n 1→ℂ) (H:Comparison.RG02.Symmetry.Orbit.Sheet r' Φ) (hK:k≤r')
    (hQ:∀ (e:ℕ),e≤ k→ ∀ v:rule (Coarse G) n, Φ e (ports G n v)=(verse (P:=P) Y s x o e v:ℂ))
include Φ hQ he ha hn hK H
open Comparison.RG02.Moving.Path
local notation "Gκ"=> verse (P:=P) Y s x o
private lemma record (L:ℝ→ Ker.rule (Coarse G) n) (he0:ContDiffAt ℝ ω L 0): patrol e Φ (C ∘ L)= ((∑ i∈range (e+1), someJ ((Gκ) (e-i) ∘ L) i):ℝ):= by
 unfold patrol; rw [Complex.ofReal_sum]; refine Finset.sum_congr rfl fun i hi=> ?_; let e':= e-i; let f:= (Gκ) e'; have h1:Plausible f:= (close_Λ T Y h ha s x o hn (show e-i≤k from (Nat.sub_le e _|>.trans he))).read; have hv':ContDiffAt ℝ ω (f ∘ L) 0:= h1.smooth.contDiffAt.comp _ he0; rw [show Φ (e-i) ∘ _=Complex.ofRealCLM ∘ (f ∘ L) from ?_]; swap; · exact funext fun i=> hQ e' ((Nat.sub_le e _).trans he) (L _)
 rw [← show someJ (Complex.ofRealCLM ∘ (f ∘ L)) i= Comparison.RG02.Moving.Path.motion (Complex.ofRealCLM ∘ (f ∘ L)) i from (by unfold motion Comparison.RG02.Assembly.jet someJ; rw [iteratedDeriv_eq_iteratedFDeriv])]; exact ((eo_Act i hv').linear (L:=Complex.ofRealCLM)).writes i le_rfl
-- Fin height guard caption.Op.Ac.L
lemma sums_true : Gκ e v= ∑ i : Fin (k+1),if i.val ≤ e then μ i.val (e-i.val) else 0:= by
 let f:= Gκ; let g(kx:ℕ):= overF (P:=P) W O Y s x o v kx (e-kx); let h1 :0<k+1:=k.zero_lt_succ
 have hm :=Fin.sum_univ_eq_sum_range (fun j=> if j≤e then g j else 0) (k+1); rw [show (∑ i : Fin (k+1),if i.val ≤ e then μ i.val (e-i.val) else 0)=_ from hm,← Finset.sum_subset (s₁:=range (e+1)) (range_mono (Nat.succ_le_succ he)) ?_]; swap; · intro i h hx; exact if_neg (mt Nat.lt_succ_of_le (mt mem_range.mpr hx))
 have ht(y:G.El):∑ j∈range (e+1),someJ ((Θ) (e-j) ∘ lifts O (o (Sonnet.root s)) y v) j = (Θ) e v:=by
    let x0:=lifts O (o (Sonnet.root s)) y v; let Phi0:= (fun _ : ℝ=> v); let L:= C ∘ Phi0; have hv':ContDiffAt ℝ ω x0 0:= necessary_shift ..; have hg:= H.follows (C ∘ x0) (fun _=> (ports G n) v) (expedition O _ y v) ((ports G n).contDiff.contDiffAt.comp _ hv') contDiffAt_const _ (he.trans hK); have ha': (∑ j∈range (e+1),someJ ((Θ) (e-j) ∘ x0) j)=∑ j∈range (e+1),someJ ((Θ) (e-j) ∘ Phi0) j:= Complex.ofReal_injective ((record T Y h ha s (x) o hn he Φ H hK hQ x0 hv').symm.trans (hg.trans (record T Y h ha s (x) o hn he Φ H hK hQ Phi0 contDiffAt_const))); rw [ha', Finset.sum_eq_single 0]; rotate_left
    · intro i _ hx; change someJ (fun (_:ℝ)=>_) i= _; exact ((Act.static (n:=i) ((Gκ) (e-i) v)).writes i le_rfl).trans (if_neg hx)
    · simp
    simp [Phi0]
 let Z':=range (e+1); rw [← Finset.sum_range_reflect]; simp only [Nat.add_sub_cancel]; let q(y:G.El) i:=W.samples y * sampler s o (lifts O (o (Sonnet.root s)) y v) (P (lap_s Y s (e-i)) x n) i; rw [show (∑ i ∈ range (e+1), (if e-i ≤ e then g (e-i) else 0))=∑ i∈range (e+1),∑ y∈W.samples.support,q y i from ?_,Finset.sum_comm]; swap
 · refine Finset.sum_congr rfl (fun i hi=>?_ ); rw [if_pos (Nat.sub_le ..)]; unfold g; rw [show e-(e-i)=i from (by have hx:= mem_range.mp hi; omega)]
 unfold q; simp_rw [← Finset.mul_sum, show ∀ y, (∑ i∈range (e+1),sampler s o (lifts O (o (Sonnet.root s)) y v) (P (lap_s Y s (e-i)) x n) i)=f e v from ht,←Finset.sum_mul, (Noon.value W)]; exact (one_mul _).symm
include hx hU hp hh ht
local notation "δ"=>dearth (a/4) n
lemma exponent_phase : Prices (lap Y s e) (topWeight (b:=b) (r:=r) T W Y t s x U k e n * dearth (a/4) n) ((grasp0 (V) o s e) - (verse (P:=P) Y s x o e)) := by
 let g:= grasp0 V o s e; let c(j: Fin (k+1)):=down₁ T W Y t n U b r s x j.val; have hc(j:Fin (k+1)):= (laneβ T W Y t h s U hU j ht hh hp).nonneg x n; rw [topWeight,mul_assoc]; apply Tracks.embark; · have hz:= T.pay_rank W O Y t h ha s x U hU hx o e; simp only [lap,Nat.zero_add] at hz; rw [sub_eq_add_neg,← neg_one_smul ℝ (Anthem.verse (P:=P) Y s x o e)]; exact Rank.add hz ((T.close_Λ Y h ha s x o hn he).scal (-1))
 intro y hy; rw [Pi.sub_apply, T.facts W O Y t h ha s x U hU hx o y, sums_true T W O Y h ha s x o y hn he Φ H hK hQ,← Finset.sum_sub_distrib, Finset.sum_mul]; apply le_trans (Finset.abs_sum_le_sum_abs ..); refine Finset.sum_le_sum fun i _=>?_ ; split_ifs with h'; · exact T.alongside W O Y t h ha s x U hU hx i o y hn he ht hy hh hp h'
 rw [sub_zero,abs_zero]; exact mul_nonneg (hc i) (Real.exp_pos _).le
end Anthem
end Bookworm
end Incline
end YM.Qlocal.Quipu.Eluder
