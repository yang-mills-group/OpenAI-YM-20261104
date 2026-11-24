import YM.GradedFar.Logged.Tips

/-!
# Every enclosing port remains clear near 0
 Use arbitrary log horizon clients with their compact bearings.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Logged.Dock
open Finset Filter Function Set Spec Table Extraction OPE.Log Asymptotics Orbits
open scoped Topology Classical BigOperators
open Economy (Paint)
variable {G:Gauge}{C:Family G}{f:Order}{S:Table C.book}
    (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {I J L:Type} [Fintype I] [Fintype J] {K:Economy.Small L} {M δ:ℝ}(hm:0≤M)(hd:0<δ)
    (x:L→I→E4)(z:L→E4) (hx:∀ᶠ i in K.p,WithinRoom (K.r i) M δ (x i) (z i))
    {bank : LogTrace F R.port}
local notation "Q"=>F.sector.derivatives
local notation "V"=>F.sector.turns
local notation "ρ"=>F.room.kernel.spin

include hm hx
lemma placed : Tendsto (fun i=> OPE.away (x i) (z i)) K.p (𝓝 (0:I→E4)) := by
    apply tendsto_pi_nhds.mpr; intro j
    apply squeeze_zero_norm' (a:=fun i=> M*K.r i)
    · exact hx.mono (fun i h=>h.1 j)
    simpa only [mul_zero] using ((tendsto_nhdsWithin_iff.mp K.leaps).1).const_mul M
include hd
lemma margined (m:ℕ) : ∀ᶠ i in K.p, orbitMargin R.port m (x i) (z i) :=
    eventually_dock R.port (placed hm x z hx) ((hx.and K.positive).mono fun i ⟨hx',hh⟩ => (show Injective _ from by
       intro j k h; by_contra U; have hsep:=hx'.2 j k U; rw [h,sub_self,norm_zero] at hsep; exact (not_lt_of_ge hsep) (mul_pos hd hh))) m
omit hm hd hx

private lemma positive_finite {J:Type}[Finite J] (f:J→ℝ)(hp:∀ j,0<f j) : ∃ c> (0:ℝ),∀ i,c≤ f i:= by
    cases isEmpty_or_nonempty J
    case inl h=> exact ⟨1,zero_lt_one,fun i=> isEmptyElim i⟩
    case inr h=> obtain ⟨i,hi⟩:=Finite.exists_min (f:=f); exact ⟨_,hp i,hi⟩

lemma turned (e:Exterior C.book): ∃ c> (0:ℝ),∀ k:Ortho,∀ z:E4, ClearOf z (swung e k z) c:= by
   let K : Type := {p:Fin e.n × Fin e.n//p.1≠p.2}
   obtain ⟨c,hc,H⟩:= positive_finite (fun j=>‖bearing e j‖) (fun i=> norm_pos_iff.mpr (Ne.symm ((beside_distinct.mp (bearing_clear e)).2.2 () i)))
   have hv p q (he:p≠q):0 < ‖bearing e p-bearing e q‖:= norm_pos_iff.mpr (sub_ne_zero.mpr ((beside_distinct.mp (bearing_clear e)).2.1.ne he))
   obtain ⟨d,hd,D⟩:= positive_finite (fun i:K=> ‖bearing e i.val.1-bearing e i.val.2‖) (fun i=> hv i.val.1 i.val.2 i.property)
   refine ⟨min c d,lt_min hc hd,fun k z=> ?_ ⟩; constructor
   · intro j; unfold swung; rw [norm_sub_rev,add_sub_cancel_left,Ortho.move_norm]; exact (min_le_left ..).trans (H _)
   intro j i h; unfold swung; rw [add_sub_add_left_eq_sub]; change min c d ≤ ‖Ortho.motion k (bearing e j) - Ortho.motion k (bearing e i)‖; rw [← show Ortho.motion k (bearing e j-bearing e i)=_ from map_sub ..,LinearIsometryEquiv.norm_map]; exact (min_le_right ..).trans (D ⟨(j,i),h⟩)
end YM.OPE.Logged.Dock
