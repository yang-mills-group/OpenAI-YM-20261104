import YM.Qlocal.Quipu.Tern
import YM.Qlocal.Quipu.Sector
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
variable (t:Senses B)(M: Vase t G i) (p:α→Site P.L) (π:ℕ→Prop)(A:Album ℕ t G i)
variable (hc: Ad G P K c)(x:Site c)(V:Ker.rule ((Coarse G⊕α)⊕RealSlice.Vertical G P K) c)
set_option quotPrecheck false
open Vase Album Arbor
local notation "T₀"=> Tern.plane P K hc
abbrev vehicle (hc:Ad G P K c) : Ω[c] → Config G (below P c):= fun v=> fine G (trees P K c) (Tern.plane P K hc v)
def tag(t:Senses B)(p:α→Site P.L)(M:Vase t G i) (hc:I₀ c) (x: Site c) (k:ℕ) (v: Ω[c]):= Arbor.mass S[c] M k p x (vehicle P K hc v) (lands P K v)
local notation "Q"=> tag P K t p M hc x k
local notation "L'"=> zstar S[c] t p x
local notation "W"=> Tern.vehicle (α:=α) P K hc
variable (FZ:Leaf c Y→Site c)
-- radius footprint in soon-cut policy. support = scope all sites.Shield.
abbrev R0 (L:Side)(a:ℕ) := a/L.val+12
local notation "o"=> R0 P.L M.momentum
private lemma gap (n l:ℕ){L:Side} (h:P.L=L): (n+l*L.val)/P.L.val=n/P.L.val+l:= by subst L; rw [Nat.add_mul_div_right n l (P.L.pos)] -- left/right
lemma belongs (k:ℕ): Requests Set.univ (tag P K t p M hc x k) Prod.fst x o:= by
 intro a _ b _ h; let m:=mapper P K G (enough P K hc);
 let L:= P.L.val; have he (i: Site (below P c)) (hp:separation L' i ≤ M.momentum+L): separation x ((S[c]).ratio.parent i) ≤ R0 P.L M.momentum:= by
    rw (occs:=.pos [1]) [show x=(S[c]).ratio.parent L' from (S[c].ratio.assemble_parent (x,p (Sonnet.root t))|>.symm)]; have hw:= bend S[c] L' i; apply le_trans hw; rw [R0]; have h1 : separation L' i / L ≤ M.momentum/L+1:= by have hx:= Nat.div_le_div_right (c:=L) hp; apply le_trans hx; exact (show (M.momentum+L)/L= _ from (by simpa only [L,one_mul] using! (gap P M.momentum 1 rfl))).le -- annotation
    change separation L' i / L + 1 ≤ M.momentum/L+12; omega
 let w := family S[c] M.stage p x
 have hh : placard w (lands P K a)=placard w (lands P K b):= by unfold placard; apply Finset.prod_congr rfl; intro j _; have h₀:= memo S[c] M.stage p x j.val j.property; apply h ((w j,pawn P K α G j.val)); exact he (Arbor.orient S[c] M.stage p x j.val) (h₀.trans (by unfold L Vase.momentum; omega))
 unfold tag Arbor.mass; split; swap; · rfl
 rw [hh, Vase.globe, Vase.globe]; refine congr_arg (· * _) (Finset.sum_congr rfl (fun j _=>?_)); refine congr_arg (_ * ·) (Finset.prod_congr rfl fun l _=>?_)
 let m₀:=M.maps l; let v:= m₀.tour; have hV : together (address T[c] G) L' (M.momentum+L) (T₀ a) (T₀ b):= by
    intro i hi; obtain ⟨i,rfl⟩:= m.surjective i
    change leaner P K a (m.symm (m i))=leaner P K b (m.symm (m i)); rw [m.symm_apply_apply]; refine h (up (Tilt.passB (G:=G) P K α α) i) (?_); change separation x i.1 ≤ _; apply le_trans _ (he (address (trees P K c) G (m i)) hi); rw [show (S[c]).ratio.parent _=i.1 from Ker.Start.live P K (enough P K hc) i]
 have hQ : travel (W a) L' (M.maps l).tour= travel (W b) L' _:= Uniform.path_same (fun j hj=> fine_read T[c] hV j (Nat.add_le_add_right (by have h₀:=M.covered l; omega : separation L' _ ≤ M.momentum) _))
 exact congr_arg (fun u:G.El=> (amend G k (M.tan l) u) (j l)) hQ
end YM.Qlocal.Quipu.Sonnet.Tern
