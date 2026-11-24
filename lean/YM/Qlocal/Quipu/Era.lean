import YM.Qlocal.Quipu.Brands
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
variable (W:Noon G N) (O:Lattice.Order) (Y: α→ℕ) (t:ℕ)(h:∀ s:Senses R,warrant k s Y N) (ha:0<a)
variable {e g:ℕ} (s:Senses R)
local notation "τ[" s "," n "]"=> lap_s Y s n
local notation "τ0[" s "," n "]"=> lap Y s n
variable (x:ι)
local notation "S[" s "," e "]"=> T.tune (lap_s Y s e) x
set_option quotPrecheck false
local notation "H0[" s "," e "]"=> (charged (k:=k) s Y (h s) (Nat.le_of_lt_succ (Fin.isLt e)))
variable (U:ℝ) (hU:0<U)(hx:U*(5*N:ℝ) ≤ a/2)
local notation "F[" n "," t "]"=> Fin (lap Y n t+1)
variable (j:Fin (k+1))(o:α→Site n)(v:rule (Coarse G) n)
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
include T h ha hn
lemma close_Λ (he:e ≤ k) : Rank Ω (lap Y s e) (verse (P:=P) Y s x o e):= by
 let q:= lap_s Y s e; have ht :q≤ N:= charged s Y (h s) he; let h0:= (T.story q x ht); let z:= (T.pays q ht|>.2).nonneg x; have hw:= Tender.charged o s.val (h0.fees _ z ha hn); exact (show q-s.val.val.card=lap Y s e from census Y s e) ▸ hw.2.1
lemma degreeL : Prices (lap Y s (Fin.val j)) (d0) (Θ (Fin.val j)-Q ((S[s,j]).typeR.table n)):= by
 have hw:= T.story (lap_s Y s (Fin.val j)) x H0[s,j]; have he:= Tender.charged o s.val (hw.2 n hn); change Prices (lap_s Y s (Fin.val j)-(essence s).card) (d0) (Q (P'- H')) at he; rw [census,Tender.tackle _ _ ((hw.fees _ ( (T.pays _ H0[s,j]).2.nonneg x) ha hn).2.1.read) ((hw.1.binding ha.le).2.1.read)] at he; exact he
variable (hv:‖v‖≤1) (hh:PaintSupply G (t+1) b) (hp:Allows (t+1) G.plog 1 r)
include hv hp hh ht he ha
local notation "f1"=> (Tracks.pawnout t (lap Y s (Fin.val j)) (leaning G n (t+1) b r))
noncomputable def growth (s:Senses R)(x:ι)(i:ℕ) := rentS W*Tender.inst s.val.val.card (lap_s Y s i)* T.fund (lap_s Y s i) x n * Tracks.pawnout t (lap Y s i) (leaning G n (t+1) b r)
local notation "W0"=> payQ s o O W (S[s,j]) v
noncomputable abbrev overF (e e':ℕ):= ∑ χ∈W.samples.support,W.samples χ* sampler s o (lifts O (o (Sonnet.root s)) χ v) (P (lap_s Y s e) x n) e'
local notation "μ"=> overF (P:=P) W O Y s x o v
local notation "Kκ"=> (growth (b:=b) (r:=r) (n:=n) T W Y t s x (Fin.val j))
lemma soldQ (hk:j.val≤e): ‖μ (Fin.val j) (e-j.val)-W0 (e-j.val)‖ ≤ (Kκ)*D:= by
 have hy:e-j.val+(lap_s Y s (Fin.val j)-(essence s).card)≤t:= by have hx: lap_s Y s e ≤ N:= charged s Y (h s) he; unfold lap_s lap at *; omega
 have h0:= T.story _ x H0[s,j]; unfold overF payQ; rw [← Finset.sum_sub_distrib]; let l:= B0 * D*c0; let C0:= l * f1; rw [show Kκ * D= rentS W*C0 from ?_,rentS,Finset.sum_mul]; swap; · unfold growth C0 l; ring
 apply (norm_sum_le ..).trans; refine Finset.sum_le_sum fun i hi=>?_ ; let y:= lifts O (o (Sonnet.root s)) i v; let f':=P'; let g:= H'; let k0:= (e-j.val); rw [←mul_sub,norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
 have hf:Rank (rule (Coarse G⊕α) n) τ f':= (h0.fees _ ((T.pays _ H0[s,j]).2.nonneg x) ha hn).2.1; have hg:Rank (rule Z n) τ g:= (h0.1.binding ha.le).2.1
 let U':= Q f'; let V':=Q g; change ‖someJ (U' ∘ y) k0 - someJ (V' ∘ y) k0‖ ≤ _; have hv':ContDiffAt ℝ ω y 0:= necessary_shift ..; have ht:someJ ((U'-V') ∘ y) k0=someJ (U' ∘ y) k0-someJ (V' ∘ y) k0:=congr_fun (some_sub (portraitMap s o hv' hf) (portraitMap s o hv' hg)) k0; rw [← ht]; exact Tracks.verity (T.degreeL Y h ha s x j o hn) (lent O _ i v hv hh hp) ( (Nat.le_add_right ..).trans hy)
include hU hx
noncomputable abbrev down₁ (n:Side)(U b r:ℝ)(s:Senses R)(x:ι)(i:ℕ):= mount (lap_s Y s i) (lap Y s i) t W n b r U a*T.d (lap_s Y s i) x + growth (b:=b) (r:=r) (n:=n) T W Y t s x i
local notation "ξ"=> (down₁ T W Y t n U b r s x (Fin.val j))
omit ht he hv hU hx ha hn in
lemma launch_pos : 0≤ Kκ := by
 unfold growth; have hg:0≤ T.fund τ x n:= (T.pays τ H0[s,j]|>.2).nonneg x n; have he : 0≤ Tender.inst (s.val.val.card) (lap_s Y s (Fin.val j)):= (Tender.valid ..).le; have hs:0≤ f1 := Tracks.pawned (leaning_ge hh hp n); unfold rentS; positivity
lemma alongside(hk:j.val ≤ e) : ‖P0 j (e-j.val) v-μ j.val (e-j.val)‖≤ ξ*dearth (a/4) n:= by
 let i:=Fin.val j; let d:=e-i; let r':= dearth (a/4) n; have hh': d+(lap_s Y s i-(essence s).card)≤ t:= by have hc: lap_s Y s e ≤ t:= ( (show lap_s Y s e ≤ N from charged s Y (h s) he).trans ht); unfold lap_s lap at *; unfold d i; omega
 let A0:= W0 d; let g:= P0 j d v; let Vq:= μ i d; apply le_trans (show ‖g-Vq‖ ≤ _ from norm_sub_le_norm_sub_add_norm_sub g A0 Vq); have hz':= (boutique s o O W (S[s,j]) (T.story _ _ H0[s,j]|>.1) ha t v H0[s,j] U hU (provided Y h ha s U hU hx j) hv hh hp hh'); refine (add_le_add (d:=Kκ*r') hz' ?_).trans (le_of_eq ?_)
 · rw [norm_sub_rev]; exact (soldQ T W O Y t h ha s x j o v hn he ht hv hh hp hk).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg (div_le_self ha.le (by norm_num))) (Nat.cast_nonneg _))) (T.launch_pos W Y t h s x j hh hp))
 unfold down₁; rw [census,add_mul] -- orientation left expression already? 
end Anthem
end Bookworm
end Incline
end YM.Qlocal.Quipu.Eluder
