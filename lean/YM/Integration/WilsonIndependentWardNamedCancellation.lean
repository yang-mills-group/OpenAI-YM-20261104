import YM.Integration.WilsonIndependentWardEulerBoard
import YM.Integration.WilsonIndependentWardRankShift

/-! Integrated Ward identities on the actual finite named R/W pair.
Only the separated specialization removes the two-link contact. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentWardNamedCancellation
open Lattice RG Wilson Source Labels WardBin PowerSeries PertExtension PertExtension.Orb XSpace XSpace.Rose XSpace.Cirrus FVA2
open FormalOPE.RG10 FormalOPE.RG10.InversionWard
open WilsonIndependentMatchedNamedPair
open WilsonIndependentWardEulerStamps
open RegulatorIR RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Halo
open scoped Classical BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(Y:Sample 2)(d:Axis)
  (k:ℕ)(label:(R.family.labels.level k).Index)(state:Bool)(o z:Cover)
local notation "T" => W.tree Y.F.p
def grade : ℕ := ((R.family.labels.level k).grades label).2
local notation "l" => grade R k label
local notation "origin" => wrap Y.F.p.side o
local notation "edge" => edgeAt (b d) origin
local notation "Z" => fun U:Config G Y.F.p.side=>euler U edge
local notation "peer" => placed R W Y state k z label
local notation "peerField" => printed R W Y state k z label
local notation "fee" f:max => Bare.normalized T G (BareOrb.stencil T (places origin f)*peerField)
local notation "received" f:max q:max => plotPT WilsonIndependentMatchedOrbitReading.originalClock
  (vital Y.F.p.side (convey o (fun _=>f) * convey z (WilsonIndependentRawNamedStencil.brand R W state k label))) (0+l) q

theorem peer_proxy : Proxy peer :=
  (field_proxy _ (sectionAt R W state k) (Pi.single label 1) (wrap Y.F.p.side z)).after Complex.reCLM Complex.reCLM.contDiff
theorem peer_local : LocalOn ((sectionAt R W state k).footprint (wrap Y.F.p.side z)) peer :=
  fun U V H=>congrArg Complex.re ((sectionAt R W state k).placed_local _ (Pi.single label 1) U V H)

variable (fit:FitsIn (scope d) Y.F.p.side)(near:avoids (edgeAt (b d) (wrap Y.F.p.side o)) (footprint (scope d) (wrap Y.F.p.side o)))
include fit near

theorem earned :
    X^l*(fee (energy d) - X^2*fee (discharge d)) =
      X^2*Bare.normalized T G (BareOrb.stencil T (coupled edge Z peer)) := by
  have H:=WilsonIndependentWardRankShift.earned T l peerField peer (ranked R W Y state k z label) edge Z
    (supplied_force (G:=G) (n:=Y.F.p.side) (b:=edge) (even_iff_two_dvd.mpr Y.F.p.even)).1
    (peer_proxy R W Y k label state z) (admitted R W Y state k z label)
  have hE:=congrArg (fun P=>Bare.normalized T G (P*peerField)) (WilsonIndependentWardEulerBoard.tree_energy (G:=G) d T origin)
  have hD:=congrArg (fun f=>Bare.normalized T G (BareOrb.stencil T f*peerField))
    (WilsonIndependentWardEulerBoard.actual_divergence (G:=G) d origin fit near)
  exact (congrArg₂ (fun a b=>X^l*(a-X^2*b)) hE.symm hD.symm).trans H

theorem all_contacts (q:ℕ) :
    received (energy d) q - (if 2≤q then received (discharge d) (q-2) else 0) =
    (coeff (l+q) (X^2*Bare.normalized T G (BareOrb.stencil T (coupled edge Z peer)))).re := by
  have h:=WilsonIndependentWardRankShift.coefficients l q _ _ _ (earned R W Y d k label state o z fit near)
  have pre:=WilsonIndependentWardEulerBoard.admissible (G:=G) d origin fit
  rw [WilsonIndependentWardNamedHearing.original R W Y k label state (energy d) o z pre.1 q,
    WilsonIndependentWardNamedHearing.original R W Y k label state (discharge d) o z pre.2 (q-2)] at h
  by_cases hi:2≤q <;> simpa [hi,grade] using congrArg Complex.re h

theorem separated (outside:off edge ((sectionAt R W state k).footprint (wrap Y.F.p.side z)))(q:ℕ) :
    received (energy d) q = if 2≤q then received (discharge d) (q-2) else 0 := by
  have H:=WilsonIndependentWardRankShift.clear T l peerField peer (ranked R W Y state k z label) edge Z
    (supplied_force (G:=G) (n:=Y.F.p.side) (b:=edge) (even_iff_two_dvd.mpr Y.F.p.even)).1
    (peer_proxy R W Y k label state z) (admitted R W Y state k z label)
    (peer_local R W Y k label state z) outside
  have hE:=congrArg (fun P=>Bare.normalized T G (P*peerField)) (WilsonIndependentWardEulerBoard.tree_energy (G:=G) d T origin)
  have hD:=congrArg (fun f=>Bare.normalized T G (BareOrb.stencil T f*peerField))
    (WilsonIndependentWardEulerBoard.actual_divergence (G:=G) d origin fit near)
  have h:=congrArg (coeff q) (hE.symm.trans (H.trans (congrArg (fun u=>X^2*u) hD)))
  simp only [coeff_X_pow_mul'] at h
  have pre:=WilsonIndependentWardEulerBoard.admissible (G:=G) d origin fit
  rw [WilsonIndependentWardNamedHearing.original R W Y k label state (energy d) o z pre.1 q,
    WilsonIndependentWardNamedHearing.original R W Y k label state (discharge d) o z pre.2 (q-2)] at h
  by_cases hi:2≤q <;> simpa [hi,grade] using congrArg Complex.re h

end YM.Integration.WilsonIndependentWardNamedCancellation
