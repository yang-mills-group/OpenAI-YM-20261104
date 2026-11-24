import YM.Qlocal.Quipu.Postage
import YM.Qlocal.Quipu.Biome
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
section shift
open Tilt Two Kinetic Floe
variable (p:Clip){ι:Type}[Nonempty ι](x:ι→PathData G)(L:ι→ℝ)
variable (Q:Push.Uniform.Before G a C P.J K (N+3)) (hB:P.Branches K G)(hx:∀ i,(x i).Bounds p a C (L i))
variable (F:ι→candidates P K G)(h:proofC P K p x Q F)
variable {δ H:ℝ} (A : PortPre P K p x b δ H)(ht:0<b)
variable (hn:Ad G P K c)
def changeTo (P:Patch) (K:KernelChoices)(G:Gauge)(α:Type): (Coarse G⊕α)⊕RealSlice.Vertical G P K ≃ α⊕(Lobby P K G):= (Equiv.sumCongr (Equiv.sumComm ..) (Equiv.refl _)).trans (Equiv.sumAssoc ..)
local notation "T♮"=> changeTo P K G α
set_option quotPrecheck false
abbrev costs (A:PortPre P K p x b δ H)(i:ι)(α:Type)[Fintype α][DecidableEq α]: Stalk ((Coarse G⊕α)⊕ J) ((Coarse G⊕α)⊕J):= Two.parallel (changeTo P K G α) (stalk P K p x A i)
-- maybe alpha not required Fintype.
variable (i:ι)
local notation "K'"=> know (costs P K p x A i α) c -- status
local notation "N'"=> know (stalk P K p x A i) c
lemma transport {U:(Ker.rule ((Coarse G⊕α)⊕RealSlice.Vertical G P K) c)} : leaner P K (K' U)= N' (leaner P K U) ∧ lands P K (K' U)=lands P K U:= by
 let H:= (T♮); let D:=stalk P K p x A i; let x (V:Ω[c]):=here (T♮).symm V; have hi(V:Ω[c]) : here Sum.inr (x V)=leaner P K V:= by funext j; rcases j with ⟨y,a|a⟩ <;> rfl
 have h'(V:Ω[c]): here Sum.inl (x V)=lands P K V:=rfl; rw [← hi,← hi,← h',← h', show x (K' U)=know (plant α D) c (x U) from Two.based D (T♮) U,site_right,site_left]; exact ⟨rfl,rfl⟩ -- notation collides local x
include h ht hB hx
lemma salaries : Belt (costs P K p x A i α) b (max (billH E J δ H) 1):= income (K:=stalk P K p x A i) T♮ (Floe.tide P K p x A ht i)
noncomputable abbrev flatten (hn:Ad G P K c) := posture (Tilt.portal G α c) (interiorL P K G hn)
local notation "Z" => flatten (α:=α) (G:=G) P K hn
-- Θ unshifted representation before orientation.Font.Art.Cap.
abbrev importation := (posture (exteriorL G c) (interiorL P K G hn)) -- variable.D
lemma advanceB (V:Ω[c]): let o:= Lapis.orbit (G:=G) T[c] (F i c); importation P K hn (leaner P K (K' V))=(colorful (fderiv ℝ o 0) (Tilt.walkB ((Z) V))).2 ∧ ((Z) V).1.2= lands P K (K' V):= by
 intro o; let x0:= A.peak i; let v:= A.deep i; let H' := rooted P K p x L Q hx F h i hn; have hh:= standing P K p x L Q hB hx A hn i; obtain ⟨hV,hQ⟩:=transport P K p x A i (U:=V); rw [hV,hQ]; exact ⟨luna _ _ _ _ H' x0 v (A.deep_bound i) (A.peak_bound i) ht.le A.nonneg.2 hh.2 hh.1 _,rfl⟩ -- check rfl flatten? `Tilt.renew` says rfl
end shift
end YM.Qlocal.Quipu.Sonnet.Tern
