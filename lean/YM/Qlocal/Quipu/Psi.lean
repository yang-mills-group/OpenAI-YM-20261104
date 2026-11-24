import YM.Qlocal.Quipu.Thermae
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
variable (i:ι)(s:Senses B)
set_option quotPrecheck false
open Arbor Album
local notation "K'"=> know (costs P K p x A i α) c -- status
local notation "Z" => flatten (α:=α) (G:=G) P K hn
lemma pinpoint (z:Ω[c]): vehicle P K hn z= Work.F03.live T[c] (Floe.slidL (G:=G) T[c] (importation P K hn (leaner P K z))) := by
 let u:= leaner P K z; let h:=enough P K hn; let Qs:= (prom P K G h)
 rw [show vehicle P K hn z=fine G T[c] (prom P K G h u) from rfl,← arb P K hn]; rfl -- slid name
local notation "φ"=> Lapis.orbit (G:=G) T[c] (F i c)
local notation "η₀"=> fderiv ℝ φ 0
local notation "θ"=> colorful (η₀)
local notation "q"=> θ ∘ Tilt.walkB ∘ Z

variable (V:Ker.rule ((Coarse G⊕α)⊕RealSlice.Vertical G P K) c)
include ht h hB hx
protected lemma mosaic (t:ℝ): let p:= Binding.gaugeL (G:=G) (trees P K c) (t•(q V)); Work.F03.live T[c] p.2 = vehicle P K hn (t• (K' V)):= by
 intro p'; have h₀:= (advanceB P K p x L Q hB hx F h A ht hn i V); rw [pinpoint]; let T':= (h₀.1); let X:=tents (Tilt.passB (G:=G) P K α α) c; rw [show leaner P K (t• (K' V))=t• leaner P K (K' V) from map_smul X _ _,map_smul,T']; rfl -- include hypothesis + notation collision
variable (U:Tale B G) (X':U.Decision) (p':α→Site P.L) {ℓ ξ:ℝ}(hU:U.Allows ℓ ξ)(hξ:0<ℓ)
include hU hξ
local notation "Hκ"=>Fin (U.depth+1)
local notation "H'[" n "]"=> Fin (Fin.val n+Lagger.dues U.power s.val + 1)
local notation "η"=> (Binding.gaugeL (G:=G) T[c] (q V))
open Comparison.RG02.Bulk
local notation "ζ"=> (Z V).1.2
lemma heavens (t:ℝ): t^(essence s).card * (∑ v:Places s c, placard v ((Z V).1.2)* posed S[c] T[c] (U.markℓ X' (Arbor.drew S[c] v p') s) (t • (Binding.gaugeL T[c] (q V))))= ∑ e:Fin (U.depth+1), ∑ r:Fin (e.val+U.boom s+1), t^U.stampE s e.val r.val * heightZ P K s p' (X' s e r) (U.array s e r) c U.method (t • K' V):= by
 let k:=(essence s).card; let W:= t • K' V; let g:= lands P K W; have hxq : lands P K W= t • (ζ):= by rw [show (Z V).1.2= _ from (advanceB P K p x L Q hB hx F h A ht hn i V).2]; exact map_smul (tents (pawn P K α G) c) _ _
 have hv (v:Places s c): t^ (essence s).card *placard v ((Z V).1.2)= placard v (lands P K W):= by rw [hxq]; unfold placard; simp only [Pi.smul_apply,smul_eq_mul,Finset.prod_mul_distrib,prod_const, Finset.card_univ,Fintype.card_coe]
 let X (x':Places s c) (e : Fin (U.depth+1)) r := U.playing X' (Arbor.drew S[c] x' p') s e r (vehicle P K hn W)
 have he(v:Places s c): posed S[c] T[c] (U.markℓ X' (Arbor.drew S[c] v p') s) (t • (η))= ∑ e:Fin (U.depth+1),∑ r:H'[e], t^U.stampE s e.val r.val*X v e r:= by
    rw [←map_smul]; let z:=Tern.mosaic P K p x L Q hB hx F h A ht hn i V t; unfold posed; rw [z]; change U.markℓ X' _ s (t*1) _= _; rw [mul_one]; rfl
 simp_rw [mul_sum, ←mul_assoc (t^(essence s).card),hv, he]; -- beware `mul_sum` RHS expands? heightZ abbrev
 simp_rw [mul_sum]; rw [Finset.sum_comm]
 refine Finset.sum_congr rfl fun e he=>?_ ; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun r hr=>?_
 let l:= U.array s e r; let M:= vehicle P K hn W
 rw [heightZ, dif_pos hn]; unfold ridge; erw [Arbor.culmination (S[c]) p' (M) (lands P K W) (X' s e r) (hU.pay s e r) hξ]; erw [mul_sum]; refine Finset.sum_congr rfl fun i hi=> ?_; exact (mul_left_comm _ _ _).trans (congr_arg _ (mul_comm _ _))
end shift
end YM.Qlocal.Quipu.Sonnet.Tern
