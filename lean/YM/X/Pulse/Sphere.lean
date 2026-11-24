import YM.X.Pulse.Bright
/-!
# reality, Unit and Signed spin of unheated stencil α families. independent of ℒ
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Pulse
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics Reed Braid
open Clove Crystal Gravity Shelf Haze Ocean Interval Size Fielding Print PertExtension LatticePT Plate
open Stems hiding X
open Crate Crate.Fund Hinge Spindle
open scoped Topology ContDiff BigOperators Classical
variable {q:ℕ+}{n:Side}{k d:ℕ}{R:ℝ}{I V T:Type*}{G:Gauge}
section spin
open Dial
variable (A:Dial.Stem (Per n)→G.Color)(P:poly (Jam n G))(s:Signed)
def gas (G:Gauge)(n:Side) : poly (Jam n G):= ∑ p:Face (Per n), hairAt p.1 (vertex p.2)
lemma retro_gas : retro (Jam n G) (gas G n)= gas G n:= by unfold gas; rw [map_sum]; simp_rw [retro_hair,retro_fire]
lemma gauge₀ : Dial.readD (0:Stem (Per n)→G.Color) P= aeval (0:Jam n G→ℂ) P:= by unfold readD; apply congr_arg fun L=> aeval L P; funext _; simp
lemma whir : Hinge.shock sale (relay s P)=Hinge.shock sale P:= by unfold Hinge.shock; rw [blend_components,blend_components,milk_relay,←gauge₀,←gauge₀, read_relay,map_zero]
lemma shines (z:Site n)(p:Curly G): Dial.readD A (hairAt z p)=snap (expandAt z A) p:= by unfold hairAt readD; rw [aeval_rename];rfl
local notation "F" => Face (Per n)
def sellS (A:Stem (Per n)→ G.Color)(v:F)(r:ℝ) := G.price (faceValue (G.lieExp ∘ (r • A)) v)
lemma sell_at (p:Face (Per n)) : sellS A p= along (Stems.Log.flame (0,p.2)) (expandAt p.1 A):= by
    funext t; unfold sellS along Log.flame; apply congr_arg; change faceValue (G.lieExp ∘ (t • A)) p=faceValue (expandAt p.1 (G.lieExp ∘ (t • A))) (0,p.2); rw [faceValue,faceValue,travel_at]; simp [faceValue]
lemma sells (p:Face (Per n)): readD A (hairAt p.1 (vertex p.2))=Complex.ofReal (Jet.someJ (sellS A p) 3):= by rw [sell_at,shines,vertex,mark_test]
lemma cost_s (p:F): sellS (Lbrush s A) p = sellS A (Face.send s 0 p):= by
    funext t; unfold sellS; rw [← map_smul,← land_exp]; exact Face.send_price (G.lieExp ∘ (t • A)) p s 0 G.price G.price_inv (fun k g ↦ G.price_conj g k)
-- ext all real arguments
lemma row_cov (p:F): relay s (hairAt (G:=G) p.1 (vertex p.2))=hairAt (Face.send s 0 p).1 (vertex (Face.send s 0 p).2):= by
    apply audible; intro a; let R(e:Dial.Stem (Per n)) : G.Color:= WithLp.toLp 2 fun i=> a (e,i); exact (by rw [read_relay,sells,cost_s,sells] : Dial.readD R (relay s (hairAt p.1 (vertex p.2)))=Dial.readD R (hairAt (Face.send s 0 p).1 (vertex (Face.send s 0 p).2)))
lemma prop_gas : relay s (gas G n) = gas G n:= by
    let e:= Equiv.ofBijective (Face.send (R:=Per n) s 0) ⟨Face.injective_send s _,(Finite.injective_iff_surjective).mp (Face.injective_send ..)⟩; unfold gas; rw [map_sum]; simp_rw [row_cov]; exact Equiv.sum_comp e (fun p:Face (Per n)=>hairAt p.1 (vertex p.2:Curly G))
-- Walk covariance
lemma spot_s (z:Cover)(t:ℝ):spot t (s.act z)= s.ortho.motion (spot t z):= by rw [Fielding.spots,Fielding.spots,map_smul,motion_st]
end spin
end YM.PositionX.Pulse
