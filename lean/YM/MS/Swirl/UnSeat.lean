import YM.MS.Swirl.Plane
/-!
# EndV waveform decision special case
 Starting Q zero. rank cap.Agree in mesh. All supplies. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Swirl
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Orbit Orbit.LogReal Orbit.Cog Book Convolve Program Puff Engine SplitP Actors Dynamics Puff.Mom
open scoped Topology ContDiff Interval
variable {A I:Type}{p:Sector A}[Fintype A] {V b:A→Cn}{Q X: SpecB A}{H:BL A}{K:Grain A}{Z: T ℂ}
    (he:Clear p K)(hv:Cog.Sym p K)(ha:∀ i,Low ( V i ))(hm:Carrier V b)(hΓ:∀ i,Green (Carrier.fees b i) K H)
    (hx:H∈ FeeP p)(hp:Pure p false H)(ht: Book.rank 2 H)(hq:Q∈ (PermV p).guard)(hQ:Γ Q p)(hz:Q 0=0)
local notation "U"=> taxi V
local notation "Ψ"=> shiftH V H
local notation "T'"=> exp0 p Q
local notation "W"=> ℶV K
local infix:70 " ⋆ "=> Actors.core (PermV p)
local notation "ϛ"=> Stuff p V H
local notation "F"=> ℶV K ( Stuff p V H )
local infix:70 " ⚘ "=> Actors.core Trunk
include he hv ha hm hΓ hx hp ht hq hQ hz
lemma ready_η (hc:Γ X p): Endμ K p Q X Z ↔ Endμ K p ( Ψ + U Q ) ( U X ) Z:= by
    have x_t : exp0 p (Ψ+ U Q)= ϛ ⋆ U ( T' ):= by unfold exp0; rw [ cheer_a (πZ (V:=V) hp ) ( taxiP V hq ) ( χ0 ha ) ( translate0 _ ha hz ), ← taxshift V Q hz ]
    unfold Endμ; rw [x_t, (PermV p).star_a, ← metra, every_T he hv ha hm hΓ hx hp ht _ ( ΤΓ_pair (expΓ hQ) hc ), every_T he hv ha hm hΓ hx hp ht _ ( expΓ hQ ),Trunk.star_a ]; exact ⟨ fun h=> by rw [h],taut Toy ( yetB (χ0 ha)) ⟩
end YM.MS.Swirl
