import YM.QuadraticLocal.Sunrise.Plaza
import YM.Push.STATIONARY_UNIFORM.Entries
/-!
 # License submission for Φ all-atom client
Exponential width **after** scaling spectral kernels on true geometry, with BEFORE-L permits
 that survive time passage later. NO W estimates here. Note Atom includes complete
 stencil; length ledger for other ancillary footprints paid during reincorporation. Γ(n) admiss.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Sunrise.Campus
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ker AllOrder.Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response AllOrder.Ink AllOrder.Ink.Method GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
open Work.F08
open Kinetic.Port
variable {G:Gauge}{n m:Side} {a k l :ℕ} (P:Patch) (K:KernelChoices)
local notation "T[" n "]" => trees P K n
local notation "S[" n "]" => dock P K n
local notation "X[" n "]"=> Positions (Primary n G)
local notation "J"=> RealSlice.Vertical G P K
local notation "E"=> Coarse G
local notation "R[" n "]" => Poll.Body (Precision.Key T[n] G)
local notation "N[" n "]" => below P n
local notation "B[" n "]"=> shores P n
local notation "I"=> Lobby P K G
local notation "Λ"=> P.L.val
local notation "I₀"=>Ad G P K
set_option quotPrecheck false
variable (u : Atom G k)(x:Site n)(v:rule (Lobby P K G) n)(hn: Ad G P K n) (hm: Ad G P K m) (p:Site P.L)
local notation "π"=>prom P K G (enough P K hn)
local notation "ξ"=> (π) v
local notation "F" => fine G T[n] (π v)

local notation "pt[" i "]"=> (shores P i).assemble
local notation "y"=> pt[n] (x,p)
variable {Θ μ V:ℝ}{i:ℕ}
local notation "k0" d:max => Campus.seatHeight P d
local notation "ν"=> (Campus.read)
local notation "a(" x ")"=> Real.exp x
local notation "H*"=>u.magnitude
local notation "μ'"=> (μ/2)
lemma palette (u:Atom G k):0≤ u.magnitude:= by unfold Atom.magnitude; positivity
include hn
lemma red (he:PaintSupply G i V)(hp:0<μ) : Allows i (ν P K u x hn p) (0 :rule (I) n) (u.budget μ*atomCost G V μ i k):=by
 obtain ⟨B,h,hB⟩:= pay_atom T[n] 1 he 0 (by simp) (pt[n] (x,p)) u hp; let z':= pt[n] (x,p); let Z:= prom P K G (enough P K hn); let X:= Z.toContinuousLinearMap; let o(x:Positions (Uniform.Joint T[n] G)):= u.unmasked (fine G T[n] x) z'; unfold signedFine at h; simp_rw [pull_id] at h; change Allows i o 0 B at h
 have hh : ‖X‖≤1:= X.opNorm_le_bound zero_le_one fun u=> by rw [one_mul]; apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr; intro j; exact norm_le_pi_norm u ((mapper P K G (enough P K hn)).symm j)
 have ht:Allows i (o ∘ X) 0 B:= by
    refine ⟨ ContDiffAt.comp _ ((map_zero X).symm ▸ h.analytic) X.contDiff.contDiffAt, fun j hj=>?_⟩
    rw [Next.Foundations.jets_linear X (h.analytic.of_le le_top)]; exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun _ _=>norm_nonneg _) (fun i _=>hh))).trans (h.norm_le _ hj))
 apply ht.mono ((le_mul_of_one_le_right h.nonneg ?_).trans hB); exact Real.one_le_exp (mul_nonneg (width_positive hp ..|>.le) (by positivity))
omit hn
def taxDoor (d i:ℕ)(μ:ℝ) (F':ℝ) : ℝ:= ((↑((crew P K G d).card^i):ℝ)* (Real.exp (μ*(i*(4*seatHeight P d):ℕ))*F')) -- G not using explicit? notation
local notation "k'"=> u.length
local notation "Tt"=>taxDoor (G:=G) P K (k') i Θ (u.budget μ * atomCost G V μ i k)
variable (h:0< Θ)(hp:PaintSupply G i V)(hM:0<μ)(ht:P.Branches K G) -- hm collision
-- post-L.U. All real n `permit.Power`
include h hp hM ht
lemma edition : ∃ H:AllOrder.Ink.Field (Lobby P K G), (∀ (n:Side)(hn: Ad G P K n) (x:Site n),H.site n x= Radial.jet (read P K u x hn p) i)∧ H.Good Θ (Tt) i:=by
 obtain ⟨d,hD⟩:= dock_larger P K ht; let t: Side:=⟨d+8*seatHeight P (u.length)+1,(by omega)⟩; let ht':= hD t (by change d≤d+8*seatHeight P u.length+1; omega); let U:= (crew P K G u.length); let v:= read P K u 0 (show Ad G P K t from ht') p; let he:= red (n:=t) P K u 0 ht' p hp hM; refine ⟨ Plaza.tile U (0:Site t) i v, fun n hn x=> Plaza.talks U x 0 i v (read P K u x hn p) (Campus.stand_in _ _ _ _ (by change 8*seatHeight P u.length < d+8*seatHeight P u.length+1; omega)) (fun p' t' k=>Campus.aligned _ _ _ _ _ hn ht' p 0 t' le_rfl k) he.analytic, Plaza.pilot _ _ _ _ he _ h.le (fun i hi=> reserved _ _ hi) ⟩ -- args
-- bind post width. Technical enough.Bio.Clock.L.T.
variable (k)
omit hp ht h
include hM
lemma surplus (A':ℝ)(h':0≤A')(n:ℕ): ∃ Z> (0:ℝ),∀ x:ℝ,0 ≤ x→ (2*x+A')^n≤ Z*Real.exp (μ*x):= by
 let v:=(μ/(n+1:ℕ)); have hz:0<v:= div_pos hM (by positivity); let Q:= 2/v+A'+1; have hQ:0<Q:=by unfold Q; positivity
 refine ⟨Q^n,pow_pos hQ n, fun x hx=> ?_⟩; let C:=Real.exp (v*x); have hv:1 ≤ C:= Real.one_le_exp (mul_nonneg hz.le hx); have hF:v*x ≤ C:= (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _); have hμ :2*x ≤ 2/v*C:= by calc
    _ = 2/v*(v*x):= by field_simp
    _ ≤ _:= mul_le_mul_of_nonneg_left hF (by positivity)
 have hP:= add_le_add hμ (le_mul_of_one_le_right h' hv); have hp:=pow_le_pow_left₀ (by positivity : 0≤ 2*x+A') (hP.trans (le_of_lt (show _ < Q*C from (by dsimp only [Q]; rw [add_mul,add_mul]; linarith)))) n
 have hh : v*(n:ℝ) ≤ μ:= (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (by omega : n ≤ n+1)) hz.le).trans_eq (div_mul_cancel₀ _ (by positivity))
 rw [mul_pow] at hp; exact hp.trans (mul_le_mul_of_nonneg_left (show C^n ≤ _ from (by unfold C; rw [← Real.exp_nat_mul]; apply Real.exp_monotone; exact (show (↑n:ℝ)*(v*x)=(v*n)*x from (by ring)) ▸ (mul_le_mul_of_nonneg_right hh hx) )) (pow_nonneg hQ.le _))
include h hp
open Laurent
local notation "Wv"=> μ
local notation "Wt"=> taxDoor (G:=G) P K
lemma stretch (hv: Θ*(4*i:ℕ)≤ μ/4*(P.L.val:ℝ)): ∃ T>(0:ℝ),∀ u:Atom G k,(Wt u.length i Θ (u.budget (μ/2) * atomCost G V (μ/2) i k)) ≤ T * u.budget μ:= by
 let L:=(P.L.val:ℝ); let K':=(Fintype.card I:ℝ); let σ:= μ/4; have hσ:0<σ:= by unfold σ; positivity
 let Φ:= atomCost G V (μ/2) i k; have hφ:0≤ Φ:= atomCost_nn hp (half_pos hM) _; obtain ⟨Z,hZ,hδ⟩:= surplus (μ:=σ) hσ (2*(4*L)+1) (by unfold L; positivity) (4*i); let Q:= Z * K'^i * Real.exp (σ * (4*L)) * Φ; have hQ:0≤Q:= by unfold Q K'; positivity
 refine ⟨1+Q,by positivity, fun u=>?_⟩; let p':=u.length; let d :ℝ:= u.length; let z:= seatHeight P u.length; have hd:0 ≤ d:= Nat.cast_nonneg _; let v' := u.magnitude; have hh₁:0≤v':= palette u
 have hz : (z:ℝ)*L≤ d+4*L:= by
   have h: (↑(z*P.L.val:ℕ):ℝ) ≤ ↑(p'+4*P.L.val:ℕ):= Nat.cast_le.mpr (show z*P.L.val ≤ p'+4*P.L.val from Nat.div_mul_le_self ..); push_cast at h; exact h -- d abbreviation cast
 have hs:(2*(z:ℝ)+1) ≤ 2*d + (2*(4*L)+1):=by nlinarith only [hz,show 1 ≤ L from (by exact Nat.one_le_cast.mpr P.L.property),show (0:ℝ) ≤ z from Nat.cast_nonneg _] -- coe syntax
 have hm' : (↑((crew P K G u.length).card^i):ℝ) ≤ (Z* Real.exp (σ*d))* K'^i:= by
    rw [seats]; push_cast; rw [mul_pow,← pow_mul]; apply mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ (by positivity) hs _).trans (hδ _ hd)) (by positivity)
 have ht : Real.exp (Θ*(i*(4*z):ℕ))≤ Real.exp (σ*d)*Real.exp (σ*(4*L)):= by
    rw [← Real.exp_add,← mul_add]; apply Real.exp_monotone
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hz hσ.le); have h:=mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg (α:=ℝ) z); push_cast at h ⊢; unfold σ L; nlinarith only [h] -- ring assoc won't linarith flatten.Nlinarith tactic
 unfold taxDoor; refine (mul_le_mul hm' (mul_le_mul_of_nonneg_right ht (by have hi:=hφ; change _≤ v'*Real.exp _ *Φ; positivity)) (by have h:=hφ; change _≤ Real.exp _*( v' *Real.exp _*Φ); positivity) (by unfold K'; positivity)).trans ?_
 have he : Real.exp (σ*d)*Real.exp (σ*d)*Real.exp (μ/2*d)= Real.exp (μ*d):= by rw [← Real.exp_add,← Real.exp_add]; apply congr_arg; unfold σ; ring
 refine le_trans (le_of_eq (show _=Q*u.budget μ from (by unfold Q Atom.budget; rw [show _ from (show ↑u.length=d from rfl),← he]; unfold Φ; ring))) (mul_le_mul_of_nonneg_right (by linarith : Q ≤ 1+Q) (by change _ ≤ v'*_; positivity))
include ht
lemma allowance (hv: Θ*(4*i:ℕ)≤ μ/4*(P.L.val:ℝ)): ∃ C:(ℝ),0 < C ∧ ∀ (u:Atom G k)(s:Site P.L),∃ H:AllOrder.Ink.Field (Lobby P K G), (∀ (n:Side)(hn: Ad G P K n) (x:Site n),H.site n x= Radial.jet (read P K u x hn s) i)∧ H.Good Θ (C * u.budget μ) i :=by
 obtain ⟨C,hC,hE⟩:=stretch k P K h hp hM hv; refine ⟨C,hC,fun u p=>?_⟩; obtain ⟨H,hH,hF⟩:= edition P K u p h hp (half_pos hM) ht; exact ⟨H,hH,hF.debt le_rfl (hE u) le_rfl⟩
end YM.QuadraticLocal.Sunrise.Campus
