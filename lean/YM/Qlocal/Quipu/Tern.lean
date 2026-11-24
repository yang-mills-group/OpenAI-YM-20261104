import YM.Qlocal.Quipu.Pal
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet.Tern
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open Further.PhysicalPeriodLimitF933 Shingle Macrame Lace
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial AllOrder Fire Laplace Laplace.SigmaP Ker Ker.Start
open Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port Tilt
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable (P:Patch)(K:KernelChoices){G:Gauge}{c r:Side}{a b C D Λ σ:ℝ}{k N l i j n m:ℕ}
local notation "T[" n "]"=> trees P K n
local notation "S[" n "]"=> dock P K n
local notation "X[" n "]"=> Positions (Primary n G)
local notation "J"=> RealSlice.Vertical G P K
local notation "E"=> Coarse G
local notation "R[" n "]" => Poll.Body (Key T[n] G)
local notation "Lℓ"=> Lobby P K G
local notation "I₀"=>Ad G P K
variable {α:Type}[Fintype α] [DecidableEq α] {B:Marker.Census α}
local notation "Y"=> ((Coarse G⊕α)⊕ J)
local notation "Ω[" n "]"=> rule ((Coarse G⊕α)⊕J) n
-- true REAL inputs Art.authorization on SOLD analytic by unshifted paint opportunity. coordinates include spect.S. Paper knows fixed phase of each slot. not arbitrary θ.
open Lasso Arbor
set_option quotPrecheck false
abbrev pawn (P:Patch)(K:KernelChoices)(α:Type)(G:Gauge)(i:α) : (Coarse G⊕α)⊕ RealSlice.Vertical G P K:= Sum.inl (Sum.inr i)
-- shorten function π, σ
variable {β:Type}[Fintype β]
abbrev tents (f:α→β)(n:Side): Ker.rule β n →L[ℝ] Ker.rule α n:= LinearMap.toContinuousLinearMap {
  toFun:= here f
  map_add':=fun _ _=>rfl
  map_smul':=fun _ _ =>rfl }
abbrev leaner (V:Ω[c]): Ker.rule Lℓ c:= here (Tilt.passB (G:=G) P K α α) V
abbrev lands (V:Ω[c]): Ker.rule α c := here (pawn P K α G) V
protected lemma tops {s:Senses B} (X:Lacing P c r n) (m:Bay s)(p:α→ Site P.L) (x:Site r): Arbor.ticket (S[r]) m p x ↔ Arbor.ticket (S[c]) m p (X.low.cut x):= by
 unfold Arbor.ticket; apply forall_congr'; intro i; apply forall_congr'; intro hi; unfold orient; rw [← show X.high.cut (bent (zstar S[r] s p x) (m.pursue i))= bent (zstar S[c] s p (X.low.cut x)) (m.pursue i) from (X.high.rooted ..).trans (congr_arg (wrap _ (m.pursue i) + ·) (X.regions ..))]; change X.R.residue _=_ ↔ X.r.residue (X.high.cut _) =_; rw [X.room]
-- concrete
variable (t:Senses B)(M: Vase t G i) (p:α→Site P.L) (π:ℕ→Prop)(A:Album ℕ t G i) (x:Site c)
-- c arbitrary; all statements before comparison.Algebra readiness. V depend.Account a.W on path occupancy all orientations. no Q*.
protected noncomputable abbrev plane (hc:I₀ c): Ω[c] →L[ℝ] Positions (Joint (trees P K c) G) := (prom P K G (enough P K hc)).toContinuousLinearMap ∘L (tents (Tilt.passB (G:=G) P K α α) c)
def ridge (hc:I₀ c) (x : Site c) (V : Ω[c]) := ∑' i', Arbor.village (S[c]) p π A (lands P K V) k (fine G (trees P K c) (Tern.plane P K hc V)) x i'
noncomputable abbrev heightZ (n:Side)(k:ℕ)(V:Ω[n]):= if hn:I₀ n then ∑ x:Site n,ridge (t:=t) P K p π A (k:=k) hn x V else 0
local notation "Q"=> Tern.plane (G:=G) P K -- ambiguous shorthand α inferred at use
variable {z : Site r}
section atlas
variable (hc:Ad G P K c) (hr:Ad G P K r)(V:Ker.rule ((Coarse G⊕α)⊕RealSlice.Vertical G P K) c)(L:Lacing P c r n)
local notation "Λ'"=> convey (α:= ((Coarse G⊕α)⊕J)) L.low
lemma empowered(x:Site r): ridge P K p π A (t:=t) (k:=k) hc (L.low.cut x) V=ridge P K p π A (t:=t) (k:=k) hr x (Λ' V):= by
 let q:= (walks P K L).governs (Q hc V); have he : Q hr (Λ' V)= (Q hc V) ∘ (walks P K L).bores:= speaking P K L (enough P K hr) (enough P K hc) (leaner P K V) -- inspect def λ
 unfold ridge; erw [he,q]; refine tsum_congr (fun i=>?_); unfold Arbor.village; split
 next h=>
    let m:=(A i).stage; let x₀:= zstar S[r] t p x; unfold Arbor.mass; have hE : L.high.cut x₀=zstar S[c] t p (L.low.cut x):= L.regions ..
    let ht:= Tern.tops P K L (A i).stage p x; by_cases hT:Arbor.ticket S[r] m p x; swap; · rw [if_neg hT,if_neg (mt ht.mpr hT)]
    rw [if_pos hT,if_pos (ht.mp hT)]
    have ht (y:Cover): L.high.cut (bent x₀ y)=bent (zstar S[c] t p (L.low.cut x)) y := (L.high.rooted ..).trans (congr_arg (wrap _ y + ·) hE)
    have hs(z:↥(essence t)) : L.low.cut (family S[r] m p x z)= family S[c] m p (L.low.cut x) z:= by
       change L.low.cut (L.R.parent _) = L.r.parent (bent _ _); erw [←L.position]; exact congr_arg _ (ht _)
    have hh : placard (family S[r] m p x) (lands P K (Λ' V))=placard (family S[c] m p (L.low.cut x)) (lands P K V):= by unfold placard; apply Finset.prod_congr rfl; intro z _; exact congr_arg (fun i=> lands P K V (i,z.val)) (hs z)
    erw [hh,Vase.read,Vase.read,L.high.expansion, (show L.high.cut _= _ from hE)]; rfl -- inspect.H
 rfl
include hr hc
lemma recruits : heightZ (t:=t) P K p π A r k (Λ' V)= (n:ℝ)*heightZ (t:=t) P K p π A c k V:= by
 unfold heightZ; rw [dif_pos hr,dif_pos hc]; rw [show (∑ x:Site r,ridge P K t p π A (k:=k) hr x (Λ' V))= _ from (show (∑ x:Site r,ridge P K t p π A (k:=k) hr x (Λ' V))=(∑ x:Site r,ridge P K t p π A (k:=k) hc (L.low.cut x) V) from Finset.sum_congr rfl fun x _=> (empowered P K t p π A hc hr V L x).symm)]; simpa only [nsmul_eq_mul] using multiplied L.low.cut L.low.fold (fun x=> ridge P K p π A (t:=t) (k:=k) hc x V)
end atlas
end YM.Qlocal.Quipu.Sonnet.Tern
