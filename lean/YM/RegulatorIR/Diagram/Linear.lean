import YM.RegulatorIR.Diagram.Valence
import YM.RegulatorIR.Budget.Draft

/-! Assembly linearity (orbit or explicit finite sum) -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Diagram
open Function Budget Budget.Layer Budget.Tuple Budget.Packet Finset
open scoped Topology ENNReal BigOperators Classical
variable {I J:Type} {r s:ℕ}
lemma symmetry_sum' (T W:Packet I r): symmetry (T+W)=symmetry T+symmetry W:= by ext1 p; simp_rw [Pi.add_apply,symmetry_at, Pi.add_apply,sum_add_distrib,mul_add]
lemma symmetry_sub (T W:Packet I r): symmetry (T-W)=symmetry T-symmetry W:= by ext1 p; simp_rw [Pi.sub_apply,symmetry_at,Pi.sub_apply,sum_sub_distrib,mul_sub]
lemma offer_sum' (f:I↪J) (T W:Packet I r): offer f (T+W)=offer f T+ offer f W:= by
 ext1 v; by_cases h:v∈Set.range (acrossT f)
 · obtain ⟨u,rfl⟩:=h; rw [Pi.add_apply,offer_eq,offer_eq,offer_eq];rfl
 rw [Pi.add_apply,offer_zero f h,offer_zero f h,offer_zero f h];simp
variable [Fintype I]
lemma loop_sub (K:Layer I I)(T W:Packet I (r+2)):loop (T-W) K=loop T K-loop W K:=by ext1 p; simp only [Pi.sub_apply,loop,curve,tsum_fintype,mul_sub,sum_sub_distrib]
lemma ray_add (K:Layer I I)(T W:Packet I r) i:ray i (T+W) K=ray i T K+ray i W K:=by ext1 p;simp only [Pi.add_apply, ray,swivel,tsum_fintype,mul_add,sum_add_distrib]
lemma draft_add (K:Layer I I)(T W:Packet I r):draft K (T+W)=draft K T+draft K W:=by
 have hh (i:List (Fin r)): drawing (T+W) K i=drawing T K i+drawing W K i := by induction i with
  | nil=>rfl
  | cons a l ih=>rw [drawing,drawing,drawing,ih, ray_add]
 unfold draft;rw [hh,symmetry_sum']
lemma knot_addR (K:Layer I I)(T:Packet I (r+1))(S W:Packet I (s+1)): knot K T (S+W)=knot K T S+knot K T W:=by
 unfold knot; rw [ray_add]; ext1 p;simp only [splice,lace,Pi.add_apply,mul_add,tsum_fintype,sum_add_distrib]
lemma knot_addL (K:Layer I I)(T W:Packet I (r+1))(S:Packet I (s+1)): knot K (T+W) S=knot K T S +knot K W S:=by ext1 p;simp only [knot,splice,lace,Pi.add_apply,add_mul,tsum_fintype,sum_add_distrib]
end YM.RegulatorIR.Diagram
