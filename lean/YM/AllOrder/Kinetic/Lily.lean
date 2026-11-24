import YM.AllOrder.Kinetic.Spirit
import YM.AllOrder.Ink.Broil
/-!
# Ticket before tilted round of pure PathData at actual G

P, K and a ledger remain the same across width calls. At all c, n (with Ad).
Output prices buy polynomial cost in Λ. Compilation into structure. Keep
winding & Mask not touched. Compare relative to supplied arbitrary plotting graph;
stable valuations unaffected by continuation choice (future).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Kinetic.Port
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable (P:Patch)(K:KernelChoices){G:Gauge}{n m:Side}{a C Λ:ℝ}{k N:ℕ}
local notation "T[" n "]"=> trees P K n
local notation "S[" n "]"=> dock P K n
local notation "X[" n "]"=> Positions (Primary n G)
local notation "J"=> RealSlice.Vertical G P K
local notation "E"=> Coarse G
local notation "R[" n "]" => Poll.Body (Key T[n] G)

abbrev exteriorL (G:Gauge) (n:Side): rule (Coarse G) n≃L[ℝ] Positions (Primary n G):= redesk (outsider G n)
abbrev interiorL (G:Gauge)(h: Ad G P K n): rule (RealSlice.Vertical G P K) n≃L[ℝ] Poll.Body (Precision.Key (trees P K n) G):=(redesk (insider P K G (enough P K h))).trans (weld _).symm
abbrev arbitrate (h:Ad G P K n) := Kinetic.posture (exteriorL G n) (interiorL P K G h)
-- `Full` differential layers
local notation "O₁"=> Lobby P K G
lemma arb (h:Ad G P K n) : (arbitrate P K h).trans (combineH (G:=G) T[n])=prom P K G (enough P K h):= by
  apply ContinuousLinearEquiv.ext; funext x i; let L:= mapper P K G (enough P K h); obtain ⟨⟨p,a|v⟩,rfl⟩:= L.surjective i
  · let B:= outsider G n; let z:=(p,a); change here Sum.inl x (B.symm (B z))=x (L.symm (L _)); rw [B.symm_apply_apply,L.symm_apply_apply]; rfl
  let B:= insider P K G (enough P K h); let z:=(p,v); change here Sum.inr x (B.symm (B z))=x (L.symm (L _)); rw [B.symm_apply_apply,L.symm_apply_apply]; rfl
variable (V : PathData G)(p:Clip)(O:ChartRatio G)
def clay (n:Side): X[n] × R[n] →ℝ:= Lapis.table T[n] (label S[n]) V p
def morn (n:Side): X[n]×R[n]→ℝ := Lapis.mist T[n] O V
def pale (n:Side): ℝ×(X[n]×R[n]) →ℝ:= Laplace.fixed T[n] O V
lemma pc (h:Ad G P K n): clay P K V p n ∘ arbitrate P K h= classicalT P K V p n ∘ prom P K G (enough P K h):= by funext i; rw [← arb P K h]; rfl
lemma s_entry (h:Ad G P K n): morn P K V O n ∘ arbitrate P K h = shadow P K O V n ∘ prom P K G (enough P K h):= by funext i; rw [← arb P K h]; rfl
lemma client (h:LocalRatio O): ∃ c, ∀ x : ℝ×(X[n]×R[n]),Real.log (pale P K V O n x)=c-morn P K V O n x.2:= by
  let c:= O.scale^Fintype.card T[n].Free; have hc:= pow_pos h.scale (Fintype.card T[n].Free); refine ⟨Real.log c,fun x=>?_⟩; rw [pale,Laplace.fixed,Real.log_mul hc.ne' (Real.exp_pos _).ne',Real.log_exp]; rfl
lemma arbC (hn:Ad G P K n) (k:ℕ):
    Ker.Start.billed P K (classicalT P K V p) k n= extractF (iteratedFDeriv ℝ (k+1) (clay P K V p n ∘ arbitrate P K hn) 0):= by rw [pc P K V p hn]; unfold Ker.Start.billed tax; rw [dif_pos (enough P K hn)]
lemma arbS (hn:Ad G P K n) (k:ℕ):
    Ker.Start.billed P K (shadow P K O V) k n= extractF (iteratedFDeriv ℝ (k+1) (morn P K V O n ∘ arbitrate P K hn) 0):= by rw [s_entry P K V O hn]; unfold billed tax; rw [dif_pos (enough P K hn)]
lemma pcs (h:Ad G P K n): Kinetic.mail (exteriorL G n) (interiorL P K G h) (clay P K V p n)= headMatrix (seedT P K p V n) := by rw [seedT,arbC P K V p h]; rfl
lemma meters (h:Ad G P K n): Kinetic.pulse (exteriorL G n) (interiorL P K G h) (clay P K V p n)=Ker.Start.pulse P K p V n:= by unfold Kinetic.pulse; rw [pcs]; rfl
end YM.AllOrder.Kinetic.Port
