import YM.RG05Readout.Aligned.Terminal

/-!
# Actual normalized densities at intermediate readout

Paid always in the finite polynomial (square-zero marker, full product),
then propagated without changing the denominator. `Captured.anchored`:
read of the one (complete-product) slot from exactly this replicated real
polynomial. Thus, in the labelled pipeline, the forward steps started
at the actual Wilson sources and the subsequent Pickup transmission to the
matching reference are on the very same density.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Aligned
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction
open MergeProof Exponential Overlay Accent MergeProof.Float PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge} {C:Family G} {N k m p d:ℕ}
variable {D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)} {u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{W:Worth}
variable {w:ℝ}
set_option quotPrecheck false
open Relay Ribbons
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
variable {f:Config G (C.side N p)→ℂ} {Q:Coefficient (C.labels.level d) (C.side k p)}
    {J:ℕ} {hk:k ≤ N} {hv:J ≤ k}
local notation "o"=> fun i=> Mix.camp C p J i
local notation "V"=> Site (C.side J p)
local notation "Bt"=> Stock.census V
local notation "u'"=> hands C p J
local notation "α'"=> march (fun _ : V=> w) φ m k
local notation "h!"=> center C.S p (hv.trans hk) 0

variable (C N k p J)
abbrev tagged (hk:k ≤ N) (hv:J≤k) (f:Config G (C.side N p) →ℂ) :=
    -- side p of same trajectory even in replication
    let F₀ := fun i:Site (C.side J p) => (center C.S p (hv.trans hk) 0).copy i f
    birth (Bt) (R N) F₀
abbrev atCut (hk:k≤ N) (hv:J≤k) (f:Config G (C.side N p) →ℂ) :=
    gust T N p N (tagged C N k p J hk hv f) k hk
variable {C N k p J}

/-- Binding `Served` to the complete grouped product `f` with
seams aligned to J. `Q` is a labelled capture representation priced at
k; comparison of DIFFERENT labels (even for same densities) needs more. -/
structure Captured (C:Family G) (N p J k d:ℕ)(hk:k ≤ N)(hv:J ≤ k)
    (f:Config G (C.side N p)→ℂ)(w:Site (C.side J p)→ℝ)
    (Q:Coefficient (C.labels.level d) (C.side k p))(c:ℝ) : Prop where
    style : Q.Format 0 C.params (C.path.rep N p k)
    pays : Q.remBound 0 (C.path.rep N p k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) c
    finite : (C.labels.level d).coeffSize Q.x ≤ c
    encoded : Served (C.path.rep N p k) (fun i=> radiant (alto C.path k d)
      (hands C p J i) (Mix.camp C p J k i) (Q.exponentialEntry 0 (C.localSection d) (C.path.rep N p k)))
      (fun i=>sunny (C.path.rep N p k) Q.forced (hands C p J i) (Mix.camp C p J k i) (alto C.path k d))
      (atCut C N k p J hk hv f) (Mix.camp C p J k)
      w (C.path.levels.budget k).supportExponent 1

namespace Captured
variable {c:ℝ}{W:Site (C.side J p) →ℝ}(h:Captured C N p J k d hk hv f W Q c)
include h

local notation "X"=> atCut C N k p J hk hv f

lemma anchored (hC:C.Makes)(U:Config G (C.side k p)) :
    ((X U).part ((Bt).fire 0)=(alto T k d) * Q.density 0 Y! (R k) U) ∧
    (X U).part (Bt).quiet=(R k|>.eval U:ℂ) := by
     let Y i:= radiant (alto T k d) (u' i) (o k i) (Q.exponentialEntry 0 Y! (R k))
     let Z i:= sunny (R k) Q.forced (u' i) (o k i) (alto T k d)
     choose a ha hS ht using fun i : V => sparkling T C.params Y! Q (u' i) (o k i) (alto T k d) hC.wilson 0 hk (hC.sections d) h.style h.pays
     have hX: Served (R k) Y Z X (o k) W (C.path.levels.budget k).supportExponent 1:=h.encoded
     rw [show Z=(fun i=> profile (R k|>.activities) (a i)) from funext ha] at hX
     obtain ⟨he,hf⟩:= hX.relay hS (hC.wilson.represents N p k hk).good.labels U
     refine ⟨(he 0).trans ?_,hf⟩
     unfold Y; rw [show coin _ _ _ _ = _ from congr_fun (ht 0) U, radiant,P_on,show (o k 0) = 0 from Ribbons.zeroMama C J p k hv]
     rw [stepid]; rfl

omit h
end Captured

section normalized
variable {I:Type} [DecidableEq I][Fintype I]{B:Census I}
variable (hC:C.Makes) (Z:I→ Config G (C.side N p)→ℂ)

include hC
/-- Moment identity for the ACTUAL pushed tagged density.
Even for the full mode and replicas; nothing here can use a lower bound on
a vacuum partition at a DIFFERENT scale/normalization. (See
`MergeProof.Accent.vista` for the rooted estimate using this principle.) -/
lemma paid_by_partition (ht : Integrable (birth B (R N) Z) (prior G (C.side N p)))
    (hk:k≤ N) (s:B.Mode) (hi:Integrable (fun U=>∏ i∈s.val,Z i U) (law G _ (C.beta N p))) :
   (∫ U,(gust C.path N p N (birth B (R N) Z) k hk U).part s∂prior G _) =
     (((∫ V₀ : Config G (C.side k p), (R k|>.eval V₀) ∂prior G _):ℝ):ℂ)*C.omega N p (fun U=>∏ i∈s.val,Z i U):=by
     let P:=birth B (R N) Z
     have h:=gust_choose T N p P ht hk s
     have hf: Integrable (fun U=>(P U).part s) (prior G _):=((Poly.get s).restrictScalars ℝ).integrable_comp ht
     refine (congr_arg (fun f:Config G (C.side k p)→ℂ=>∫ U,f U ∂prior G _) h).trans
            ((GridApprox.pushTo_integral T N p hk _ hf).trans ?_)
     rw [History.partition_eq C.path hC.wilson N p k hk,Family.omega,moment_formula _ _ hi]; unfold Family.beta; rw [mul_inv_cancel_left₀ _ _]
     · unfold P; simp_rw [MergeProof.Accent.birth,(hC.wilson.starts ..).2,Poly.part_smul,Mach,Extra.Trajectories.pass_fire]
     exact Complex.ofReal_ne_zero.mpr (partition_pos _).ne'

end normalized
end YM.RG05Readout.Aligned
