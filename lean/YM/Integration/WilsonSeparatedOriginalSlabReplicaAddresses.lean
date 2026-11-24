import YM.Integration.WilsonSeparatedOriginalReplicaSupport
import YM.Integration.WilsonSeparatedOriginalProfilePortfolio
import YM.RG05Readout.Pulse.Openly

/-! The genuine centered torus parent cells on the whole replicated conditional, before taking any absolute values. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalSlabReplicaAddresses
open Function Finset Matrix MeasureTheory Lattice RG Wilson RG05Readout Source Address Push Local Marker MergeProof
open RG05Readout.Flatten RG05Readout.Native RG05Readout.View RG05Readout.Pulse
open Extra.Histories PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
open RG05Readout.Pulse RG05Readout.Flatten
open private taboo from YM.Integration.WilsonSeparatedOriginalReplicaSupport
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{b N p:ℕ}
local notation "V"=>Fin 3
local notation "A"=>C.S.a
local notation "Λ"=>C.S.toDepth
local notation "X!"=>C.side N p
local notation "G!"=>C.S.gridPoint
local notation "o!"=>C.S.place
local notation "ρ₀"=>C.S.radius p
local notation "J!"=>Cloud V

variable (h:b ≤ N)(s:V→ℕ)(v:(i:V)→Palette C (s i))(Ψ: Wave V)(u:V→Site (C.side b p))
local notation "r"=> Λ h p
local notation "T"=> Site (r).count
local notation "S"=> WilsonSeparatedOriginalReplicaWave.scalp (C:=C) s v u h
local notation "q!"=> (fun o:V→Site X!=> WilsonSeparatedOriginalReplicaWave.harpoon (C:=C) (N:=N) (p:=p) s v o)
-- Relative packet in shape Φ on support
variable (q:ℝ)(hq:0<q)
local notation "Z"=> fun x=> cropX Ψ u q x
local notation "M!"=> cameo C p N q Ψ
-- compute through a projected slot root tuple. z base center
variable {B R:ℝ}(hΨ:∀ x∈tsupport Ψ.val,∀ i:V, ‖x i‖≤R)(z:Site (C.side b p))(x:E4)(hx:x∈Native.box)(hz:‖voyager C p b z x‖≤ B)
local notation "K!"=> (r).count.val
local notation "t₁"=> voyager C p b z x
local notation "U"=> fun w:V→T=> (fun i:V=> (r).assemble (u i+z,w i))
local notation "V!"=> fun w:V→T=> (fun i:V=> offset h z (u i) (w i))
local notation "Φ"=> fun w:V→T=>fork ((↑K!:ℝ)⁻¹) (fun i:V=>placeR (r) (w i)) (Z x)
include hq hΨ hx hz
theorem original (w:V→T)(hp:q*R+2*(A b)<ρ₀)(hρ:B+q*R<ρ₀): WilsonSeparatedOriginalReplicaWave.harpoon (C:=C) (N:=N) (p:=p) s v (U w) (Φ w)= WilsonSeparatedOriginalReplicaWave.harpoon (C:=C) (N:=N) (p:=p) s v (U w) (M! t₁ (U w)):=by
   rw [mask_test]; unfold cameo; let W:=(U w); let a :=fun i:V=> q⁻¹ • (G! N (V! w i)- t₁); let b': J!:=fun i=> q⁻¹ • (o! (W i)- t₁); change q! W (fork _ a Ψ)= q! W (fork _ b' Ψ)
   by_cases he: a∈tsupport Ψ.val
   · have hE: b'=a:=by funext i; unfold b' Schedule.place; rw [show lift (W i)= (V! w i) from from_lift h z x _ _ hz (aperture q R _ _ hq (hΨ _ he i)) hρ]
     rw [hE]
   by_cases hg:b'∈ tsupport Ψ.val
   · have hE:b'=a:=by funext i; unfold b' Schedule.place; rw [show lift (W i)= (V! w i) from from_root h z x hx _ _ (aperture q R _ _ hq (hΨ _ hg i)) hp]
     rw [hE]
   exact Eq.trans (taboo s v W _ Ψ _ he) (taboo s v W _ Ψ _ hg).symm

end YM.Integration.WilsonSeparatedOriginalSlabReplicaAddresses
