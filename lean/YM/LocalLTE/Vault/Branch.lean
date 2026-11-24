import YM.LocalLTE.Vault.Crown
/-!
# Independent stencil cut for products, with currency specified per site
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Vault
open Finset Function Filter Lattice Wilson RG Source Labels Extra.Histories Motion
open LocalLTE.Vinca LocalLTE.FrameBox AnalyticBridge VerifiedReset Collection Price PhysicalNext.Repeat Blush
open Push Local Planned.GuardedAtom LocalLTE.River YM.MergeProof
open LocalLTE.Port ConnectedActivityE6 Blaze -- ambiguity remove
open AbsoluteSums Animals Next.Foundations
open Finset MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Interval Classical
variable {G:Gauge}{n:Side}
attribute [local instance] Gauge.frobInner
noncomputable def strut {o: Site n}(κ:ℝ)(A:Grove o)(s k:ℕ)(f:Config G n→ℂ):Config G n→ℂ:= ∑ i:Bool,(Hue 1 i) ∘ Hall.shave A s κ k (Port.scaleQ i∘ f)
variable (f:Config G n→ ℂ) (Z:Grove (0:Site n)){s k:ℕ}{x κ :ℝ}{P:BudgetPoint}(hp: Reliable G κ x)
local notation "Q"=> strut κ Z s k f
variable {b u:ℝ}
set_option quotPrecheck false
local notation "W" => neighbors s (0:Site n)
local notation "W'"=> neighbors (s+1) (0:Site n)
lemma strutPowers (i:Bool): Replicated Z s κ k (Port.scaleQ i ∘ Q):=by
    let q (i:Bool):= Hall.shave Z s κ k (Port.scaleQ i ∘ f); let g i:= Hue 1 i ∘ q i
    have h j:Replicated Z s κ k (Port.scaleQ i ∘ g j):= huesPam Z (q j) k (show Replicated Z s κ k (q j) from ⟨_,rfl⟩) 1 j i
    rw [show Q=(g true+g false) from Fintype.sum_bool _, show Port.scaleQ i∘ (g true+g false)= (Port.scaleQ i ∘g true)+(Port.scaleQ i∘ g false) from funext (fun x=>map_add ..)];exact rp_add Z (h true) (h false)
variable (hF:P.Regular (neighbors s (0:Site n)) f)(hB:P.supBounds 0 (neighbors s (0:Site n)) f b)
include hp hF hB
lemma strutFits (h: ∀ i:Bool,ContDiffAt ℝ (↑k) ((Port.scaleQ i ∘f) ∘ FrameBox.Grove.soloV) 0) (hδ:∀ i:Bool,P.supBounds 0 (neighbors (s+1) (0:Site n)) ((Port.scaleQ i ∘ f)- Hall.shave Z s κ k (Port.scaleQ i ∘ f)) u)(he:0<k):
    P.Regular W' (Q)∧P.supBounds 0 W' (Q) (b+2*u)∧ P.supBounds 0 W' (f-Q) (2*u)∧ (Q) 1=f 1:=by
    let y(i:Bool):= Port.scaleQ i ∘ f; let q(i:Bool):=Hall.shave Z s κ k (y i);let t i:= Port.Hue 1 i ∘ q i; let v i:= Port.Hue 1 i ∘ y i
    have hv : f=v true+v false:=by
        funext U; unfold v y; apply Complex.ext <;> simp [Port.scaleQ,Hue,ink] -- orientation sign
    have ht : Q=t true+t false:=Fintype.sum_bool _
    have hX : neighbors s (0:Site n)⊆ W':=fun i hi=> (neighbors_mem ..).mpr (((neighbors_mem ..).mp hi).trans (Nat.le_succ s))
    have hf(i:Bool):P.Regular W (q i):=FrameBox.legal _ _ hp _ _
    have hY(i): P.Regular W (y i):= (Port.framesV hF hB i).1
    have hU(i): P.Regular W' (t i):= Port.hueReg _ P _ (AnalyticBridge.VerifiedReset.reg_larger (hf i) hX) _ _
    have hA:P.Regular W' Q:=ht.symm ▸ regular_add (hU true) (hU false)
    have hs:= Next.Foundations.regular_larger hF hX; have hX' i:v i-t i=Hue 1 i ∘ (y i-q i):=Port.hueDiff _ _ _ _
    have hy(i):P.Regular W' (y i-q i):= AnalyticBridge.VerifiedReset.reg_sub (VerifiedReset.reg_larger (hY i) hX) (VerifiedReset.reg_larger (hf i) hX)
    have Hh: P.supBounds 0 W' (f-Q) (2*u):=by
        have hZ(i): P.Regular W' (v i-t i) ∧ P.supBounds 0 W' (v i-t i) u:=by rw [hX']; exact ⟨Port.hueReg _ P _ (hy _) _ _,by simpa only [norm_one,one_mul] using Port.hueRad _ P _ (hy _) 1 i 0 (hδ i)⟩
        rw [ht,hv, show v true+v false-(t true+t false)=_ from (show _=(v true-t true)+(v false-t false) from (by abel)), two_mul]; exact Next.Foundations.bound_add (hZ _|>.1) (hZ _|>.1) (hZ _|>.2) (hZ _|>.2)
    have hx:= bound_sub hs (Next.Foundations.regular_sub hs hA) (bound_larger hB hX) Hh; rw [sub_sub_cancel] at hx
    refine ⟨hA,hx,Hh,?_⟩
    have hp (i):t i 1=v i 1:=by
        apply congr_arg (Hue 1 i); let B:Directions G n:=0
        have he:= Hall.roots _ Z hp _ P (y i) (hY i) (h i) 0 he -- args
        have hx:= congr_arg (fun q:(Directions G n)[×0]→L[ℝ] ℝ=> q fun _=> B) he
        simpa [q,iteratedFDeriv_zero_apply] using hx
    rw [ht,hv,Pi.add_apply,Pi.add_apply, hp, hp]
end YM.LocalLTE.Vault
