import YM.Qlocal.Quipu.Bookworm
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
include ha hU hx h
local notation "F[" n "," t "]"=> Fin (lap Y n t+1)
variable (j:Fin (k+1))(o:α→Site n)(v:rule (Coarse G) n)
local notation "C"=> ports G n
set_option quotPrecheck false
abbrev layout : Tale R G := Stanza.son (plan T Y O h W x) t
local notation "V"=> layout T W O Y t h x
local notation "A0"=> fun (_ : ℕ)=>True
noncomputable abbrev statement (M:Tale R G): M.Decision:= fun _ _ _ _=>True
noncomputable abbrev grasp0 (M:Tale R G)(o:α→Site n) (s:Senses R) (i:ℕ)(v:rule (Coarse G) n) := Radial.jet (fun (u:ℝ×fieldDir G n 1)=> M.markℓ (statement M) o s u.1 (represent u.2)) (i+M.boom s) (1,ports G n v)
abbrev reading (v:rule (Coarse G) n)(i:Fin (k+1))(r:F[s,i]) := fun t':ℝ=> t'^ ((V).stampE s i r)* (V).playing (statement (V)) o s i r (passing v t')
local notation "w"=> dues Y s.val
abbrev datum (e': Fin (k+1))(k₁:ℕ)(x0:rule (Coarse G) n):= litT s o O W (T.tune (lap_s Y s e') x) (T.story _ x (H0[s,e'])|>.1) t x0 H0[s,e'] k₁
local notation "P0"=> datum T W O Y t h s x o
abbrev verse (e':ℕ) := crystal R s.val o (P (lap_s Y s e') x n)
local notation "Λ"=> fun i r=> (V).array s i r
open Comparison.RG02.Assembly (GradeAt)
-- Lemma order.Sign full-layout implements forecast
lemma read_r (i:Fin (k+1))(r: Fin (lap Y s i+1)): GradeAt (lap Y s i) (reading T W O Y t h s x o v i r):= by
 let w':=V; let M:= (V).playing (statement (V)) o s i r; let L:= M ∘ passing v; have he : GradeAt r.val L:= Album.rank (x:=o (Sonnet.root s)) (p:=fun k=> True ∧ Bay.Hears (((V).array s i r k).stage) o) ((V).array s i r) t (passing v) (blank_here v) (T.charging W O Y h ha s x U hU hx i r) hU (three_happy _)
 rw [show reading T W O Y t h s x o v i r=(fun t':ℝ=>t'^(w'.stampE s i r))*L from rfl]; exact ((GradeAt.shifts (fun t':ℝ=>t') contDiffAt_id rfl (w'.stampE s i r)).mul he).lower (by change _ ≤ (lap Y s i-r.val+r.val); omega) -- w notation collides local, fix
lemma elsewhere (i:Fin (k+1))(r: Fin (lap Y s i+1))(he:e < i.val): someJ (reading T W O Y t h s x o v i r) (lap Y s e)=0:= by unfold someJ; let heq:= T.read_r W O Y t h ha s x U hU hx o v i r; rw [iteratedDeriv_eq_iteratedFDeriv, heq.vanish _ (Nat.add_lt_add_right he _)]; simp
lemma arch_eq (i:ℕ) : grasp0 V o s i v=someJ (fun t':ℝ=> (layout T W O Y t h x).markℓ (statement (V)) o s t' (passing v t')) (i+dues Y s.val):= by
 let X':= V; let u:= statement X'; let H:= X'.boom s; let f:= fun (u':ℝ×fieldDir G n 1)=> (V).markℓ u o s u'.1 (represent u'.2); let p:ℝ×_ :=(1,(ports G n v)); have hl:ContDiffAt ℝ ω f 0:= (X'.quartile s o (T.health W O Y t h ha x U hU hx) hU u).zeroAt.smooth
 rw [grasp0,← jet_entry (h:=f) (n:=i+H) (hl.of_le le_top) p]; apply congr_arg (fun f:ℝ→ℝ=>someJ f _); ext x; simp only [f,passing,Prod.smul_fst,Prod.smul_snd,p, smul_eq_mul,mul_one]; rfl
local notation "R1"=> reading T W O Y t h s x o v
lemma worth_head (i:Fin (k+1))(he:i.val≤e) : ∑ r:F[s,i],someJ (R1 i r) (e+dues Y s.val) = P0 i (e-i) v := by
 let Y':= S[s,i]; have hv(r):ContDiffAt ℝ ω ((V).playing (statement (V)) o s i r ∘ passing v) 0:= (Album.rank (x:=o (Sonnet.root s)) (p:=fun k=> True ∧ Bay.Hears (((V).array s i r k).stage) o) ((V).array s i r) t (passing v) (blank_here v) (T.charging W O Y h ha s x U hU hx i r) hU (three_happy _)).smooth; unfold datum litT; rw [census]
 refine Finset.sum_congr rfl fun r hr=>?_ ; let p:= ((V).stampE s i r); erw [show reading T W O Y t h s x o v i r = (fun t':ℝ=>t'^p)*((V).playing (statement (V)) o s i r∘ passing v) from rfl, jo_shift (hv r) p,if_pos (show p≤lap Y s e from (Nat.sub_le (lap Y s i) r.val).trans (Nat.add_le_add_right he _)), show lap Y s e-p=e-i.val+r.val from ?_] -- semir.expr conflict
 · rfl
 change e+dues Y s.val-(lap Y s i - r.val)=e-i.val+r.val; have he':r.val ≤ lap Y s i:= Nat.le_of_lt_succ r.isLt; unfold lap at *; omega
lemma facts (e:ℕ) : grasp0 (V) o s e v= ∑ i:Fin (k+1), if i.val≤ e then P0 i (e-i) v else 0 := by
 rw [arch_eq T W O Y t h ha s x U hU hx]; let f(i:Fin (k+1)):=R1 i; change someJ (fun t:ℝ=> ∑ i: Fin (k+1),∑ r:F[s,i], f i r t) (e+dues Y s.val)=_; have ht(i:Fin (k+1))(r:F[s,i]):ContDiffAt ℝ ω (f i r) 0:=(T.read_r W O Y t h ha s x U hU hx o v i r).smooth
 rw [billJ _ (fun i hi=> ContDiffAt.sum (f:= f i) (fun j _=> ht i j) )]

 refine Finset.sum_congr rfl fun i hi=>?_ ; rw [billJ _ (fun j _=> ht i j)]; split
 next hl=> exact worth_head T W O Y t h ha s x U hU hx o v i hl
 next hl=> exact Finset.sum_eq_zero fun r _=> elsewhere T W O Y t h ha s x U hU hx o v i r (by omega)
-- rank for U.S.T.Moment.Real
lemma pay_rank (j:ℕ): Rank Ω (j+lap Y s 0) (grasp0 V o s j) := by
 rw [show j+lap Y s 0=j+dues Y s.val from congr_arg (j + ·) (Nat.zero_add _)]; let n₀:= j+dues Y s.val; let γ0:= (C).toContinuousLinearMap; let F : ℝ×fieldDir G n 1→ℝ:= (fun q=> (V).markℓ (statement V) o s q.1 (represent q.2)); let H:= Radial.jet F n₀; have ht: Rank (ℝ× fieldDir G n 1) n₀ H:= (Rank.hom (ContinuousLinearMap.id ℝ _) (iteratedFDeriv ℝ n₀ F 0)).scal _
 let p : rule S n →L[ℝ] ℝ×fieldDir G n 1 := (ContinuousLinearMap.inr ℝ _ _) ∘L (ports G n).toContinuousLinearMap; convert ht.app p ((1:ℝ),0) using 1; ext1 i; simp [p,grasp0]; rfl
end Anthem
end Bookworm
end Incline
end YM.Qlocal.Quipu.Eluder
