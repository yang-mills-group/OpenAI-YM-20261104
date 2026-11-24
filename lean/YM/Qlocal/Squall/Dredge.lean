import YM.Qlocal.Feud.AmberP
import YM.Qlocal.Squall.Plunge
/-!
# Horizon supply. Plan projections on *all* orientations from one
 paid family.Any polynomial in size within host.We call on all actors after width finance, with input unitized to preserve budgets under repetition (not assumed here). Blade.Frame.B.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Squall
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function
open AllOrder Floe Step Step.PlanV Iron
open Response Ink Ink.Method Ink.Money
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port Pace PriceCompiler Further.PhysicalPeriodLimitF933
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{A:Stage}{U:MapPrices}{K:KernelChoices}{ι:Type} [Nonempty ι]
namespace Dredge
open Aero StateE Rent Laurent Shingle Macrame PhysicalNext ThroughLaunch Pane Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Quipu Quipu.Tilt Quipu.Sonnet Tern Quipu.Eluder Incline Incline.Bookworm
private lemma credit_shift {V V':Type} {Γ p:V→ℝ}{j:ℕ}(H:CreditF Γ j p)(X:V'→V): CreditF (Γ∘X) j (p∘ X):= by rcases H with ⟨d,h,d'⟩; exact ⟨d,h,fun i=>d' (X i)⟩
variable {X:Org.Metals G}
variable (D:RG.Supply.Rolls X.p)(R:Roots (G:=G) X.p.profile X.K X.p.kernel)(x y k N:ℕ) (hx:4≤x) -- x stage fine from D
set_option quotPrecheck false
local notation "A"=> X.p.profile
local notation "p"=> (A x).clip
local notation "K"=> X.p.kernel
local notation "O"=> X.O
set_option quotPrecheck false
local notation "S"=> Mural.sheet X.p D hx
local notation "I"=> Card D R x y hx k
local notation "T"=> Age.scope (k+2)
variable (W:ι→Card D R x y hx k)
variable (α:Type)[Fintype α][DecidableEq α] {B: Marker.Census α} (g:α→ℕ){m n u t r l : ℕ} {b d:ℝ}
variable (Ψ:ι→ Stanza B G g m)(Y:∀ i,(Stanza.son (Ψ i) u).Decision) (ρ:ι→α→Site (D.L x)) (c:ι→ℝ) -- Θ.Seats
local notation "L"=> fun i:ι=> (W i).self.north
local notation "Γ"=> fun i:ι=> (W i).self.paid
local notation "Θ"=> fun i:ι=> (W i).extra
abbrev Bent (k:ℕ) :ℕ:= 1+(Age.scope (k+2)).sup (fun v=> level k v+1)
local notation "n'"=> (Bent k)
noncomputable abbrev δ (G:Gauge)(X:Org.Metals G)(R:Roots (G:=G) X.p.profile X.K X.p.kernel)(x k N:ℕ):ℝ:= Prior.core R k N x
local notation "δ₀"=> Prior.core R k N x
local notation "μ"=> Prior.yard R k N x
local notation "μ'"=> Prior.yard R k N y
local notation "u'"=> insure δ₀ N (n')
-- Lease.J obeys spacing. t may be larger init method of Forecast. Builder does NOT assume same k as Memo Warden. Does not assume analytic cost already funds Motion.
variable (hV: CreditF (fun i:ι=> (W i).self.paid) (Bent k) c) (hP:∀ i:ι,(Stanza.son (Ψ i) u).Allows (Prior.yard R k N x) (c i))
    (hr:∀ s:Senses B,warrant r s g N) (ht:N≤ t)
    (hY:StepStages x y)(hN:2 ≤ N) (h:Prior.Awning R x (↑(D.L x).val:ℝ)) (hσ:N ≤ x)(hz:k ≤ x)
include hP hV hr ht hY hN hσ h hz W
lemma berth : ∃ (S':ι→Stanza B G g r) (b':ι→ℝ) (D':ℕ→ Senses B→ι→Side→ℝ), Tilt.Certificate (b:=Prior.core R k N x) (l:=Bent k) (N:=N) (Mural.sheet X.p D hx) X.p.kernel (X.p.profile x).clip X.O (fun i:ι=>(W i).self.north) (fun i:ι=>(W i).extra) (Age.scope (k+2)) (fun i:ι=>(W i).self.paid) α g Ψ Y ρ r t (4*Prior.yard R k N y) S' b' D':= by
 let D':=baseS (G:=G) X.K X.p.kernel x; have ha : ((S).Branches K G):= X.p.has (S)
 obtain ⟨Q⟩:= Plateau.Art.has (G:=G) (N:=N) (S) (K) (A x) (by omega)
 let hU:=fun i:ι=>(W i).self.upCost
 obtain ⟨F,hF⟩:=tens (S) K (p) L Γ Q hU
 obtain ⟨A'⟩:= tracks S K (p) L Γ Q ha hU D' (Card.up∘ W) (fun i=>(W i).att1) (fun i=>(W i).metric1) (fun i=>(W i).floor1) (fun i=>(W i).sworn1)
 have hg:CreditF Γ 1 Γ:= givenC (fun i=> budget_nonneg ((W i).self.upCost.two))
 obtain ⟨U⟩:= decay S K p L A' (Prior.schooling R k N x)
 have hv(v:Age)(hi:v∈T) :request (δ₀) (Γ) (n') N (Θ) v:= by
    have hy : level k v+1 ≤ Bent k:= (Finset.le_sup (f:=fun i=> level k i +1) hi).trans (Nat.le_add_left ..)
    have hQ : Nonempty (I):= ⟨ W (Classical.arbitrary _)⟩
    exact ⟨fun i=>authority k v ((W i).self.paid), R.pre k x v,(R.shape k|>.pos x v),credit_shift (((allowance_f D R x y hx) v hi |>.1).up hy) W, Prior.ages _ _ _ _ _ hi,fun i=> ((W i).quote v hi).pay⟩
 exact Tilt.runway S K p O L Γ Q ha hU X.oga F hF (Θ) T (fun i=>audited D R x y hx (W i)) Γ U (Prior.core_p ..) ((Prior.schooling ..).trans (min_le_left ..)) (hg.up (Nat.le_add_right 1 _)) hv α g c Ψ Y ρ (Prior.yard_p ..) hV hP (Prior.feeds R k N x h hz hσ) r t (4*μ') hr (mul_pos (by norm_num) (Prior.yard_p ..)) (Prior.earns R k N x y hY) ht
end Dredge
end YM.Qlocal.Squall
