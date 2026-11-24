import YM.SharpGram.Load.Tents
import YM.Trace2.Orthogonal

/-! Multiplicity-one traceless stress probes. No estimates on stress
trace, nor replacing stress with traceless in charges. The *image through them*
of all orbit-equivariant operators calculated on actual and free metrics will
be controlled. Uses complete rotation-work d4 in true S labels. Complex
normalization here and in emitted functionals.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Load
open Function Filter Set Table Climb Analysis Org Extraction Spec Next.UVStress Maxwell
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G: Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}
open UVNext.FreeStress
section sub
variable {L:Register G}{S:Table L}(R:S.Rotation)
structure traceless (J:S.Stress): Prop where
   tensor : Tensorial R J
   sym (i j:Axis): J i j=J j i
   trace : ∑ i:Axis,J i i=0
variable {R} {J K:S.Stress} (h:traceless R J)
include h
lemma traceless.add (ht:traceless R K) : traceless R (J+K) := by
    refine ⟨fun p i j=> ?_,fun i j=> congr_arg₂ (·+·) (h.sym i j) (ht.sym i j),?_⟩
    · simp_rw [Pi.add_apply,map_add,h.tensor _ i j,ht.tensor _ i j,smul_add,Finset.sum_add_distrib]
    simp_rw [Pi.add_apply,Finset.sum_add_distrib,h.trace,ht.trace,add_zero]
lemma traceless.scale (c:ℂ) : traceless R (c • J):= by
    refine ⟨fun p i j=> ?_,fun i j=> congr_arg (c • ·) (h.sym i j),?_⟩
    · simp_rw [Pi.smul_apply,map_smul,h.tensor p i j,Finset.smul_sum]; simp_rw [smul_comm c]
    simp_rw [Pi.smul_apply, ← Finset.smul_sum,h.trace,smul_zero]
lemma traceless.reflect (H : S.Hierarchy) {V : DiffPlan S} (he:R.Laws V H.spin) : traceless R (UVNext.FreeStress.pulsed H J) := by
    refine ⟨fun p i j=> ?_, fun i j=> congr_arg _ (h.sym i j),?_⟩
    · unfold pulsed; rw [← he.real,h.tensor]; simp only [map_sum,map_smulₛₗ]; simp
    unfold pulsed; rw [← map_sum,h.trace,map_zero]
lemma traceless.remove (ht:traceless R K): traceless R (J-K):=by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ K]; exact h.add (ht.scale _)
omit h
-- Stress trace canceled with exact δ addition? define linear map from Stress.Launch
abbrev sumTrace (D:S.Stress):=∑ i : Axis,D i i
def delta (J:S.Stress)(i j:Axis): S.Field 4 := J i j-(if i=j then (1/4:ℂ) • sumTrace J else 0)
lemma unityO (s:Ortho)(i j:Axis) : (∑ a : Axis,(↑(s.val a i * s.val a j):ℂ))=if i=j then 1 else 0:= by
    have h : star s.val * s.val=1:= s.property.1
    have he := congr_arg (fun w:M4=> (w i j:ℂ)) h
    simpa [Matrix.mul_apply,Matrix.star_apply,Matrix.one_apply,apply_ite Complex.ofReal] using he
lemma unityO_back (s:Ortho)(i j:Axis) : (∑ a : Axis,(↑(s.val i a * s.val j a):ℂ))=if i=j then 1 else 0 := unityO s⁻¹ _ _
lemma tensorTrace (h: Tensorial R J)(s:Ortho) : R.act 4 s (sumTrace J)=sumTrace J:=by
   unfold sumTrace; simp_rw [map_sum,h s]
   let u(i a b : Axis) : S.Field 4:= ( (↑(s.val a i * s.val b i):ℂ) • J a b )
   rw [Finset.sum_comm]
   refine Finset.sum_congr rfl fun i _=> ?_
   rw [Finset.sum_comm]; change (∑ b:Axis,∑ a:Axis,u a i b)= _
   simp only [u,← Finset.sum_smul,unityO_back,ite_smul]; simp
lemma delta_traceless (ht: Tensorial R J)(h:∀ i j, J i j=J j i) : traceless R (delta J):= by
    have hv (s : Ortho)(i j : Axis) : R.act 4 s (delta J i j) = ∑ a:Axis,∑ b:Axis,(↑(s.val a i*s.val b j):ℂ) • delta J a b:= by
       unfold delta; simp_rw [map_sub,apply_ite (R.act 4 s),map_zero,map_smul, ht _ i j,tensorTrace ht,smul_sub, smul_ite,smul_zero,Finset.sum_sub_distrib]; simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
       rw [← Finset.sum_smul,unityO,ite_smul];simp
    refine ⟨hv, fun i j=> by unfold delta; rw [h i j]; simp only [eq_comm (a:=i) (b:=j)], ?_⟩
    unfold delta; rw [Finset.sum_sub_distrib]; simp only [if_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin];
    rw [← Nat.cast_smul_eq_nsmul ℂ]; unfold sumTrace; push_cast; module
end sub
local notation "S'"=> Bel C.book
local notation "V"=> F.sector.derivatives
local notation "V'"=> Maxwell.Free.scheme C.labels
local notation "σ" => Maxwell.Free.spin_free C.labels
local notation "E" => Maxwell.Free.gear C.labels
local notation "α" => F.sector.turns
local notation "T" => F.phase.transport
local notation "T0"=> UVNext.FreeStress.canonicalStress C.labels
local notation "H"=> Maxwell.Free.hierarchy C.labels
variable (hG:G.Simple)
section base
include hG
lemma single : traceless E T0 := by
   obtain ⟨M,h1,h2,h3,ht,hs⟩:=chosen_lit (C:=C) hG
   have h: M.T.J=T0 := by rw [h3,torch,one_smul]
   refine ⟨h2 ▸ h ▸ ht,fun i j=>?_,?_⟩
   · rw [← h]; exact hs.origin.symmetric ..
   simpa only [torch,one_smul] using Trace.torch_traceless C.labels 1
lemma can_lit : T0≠0 := by
   rw [← lighting C.labels σ]; exact fun h=> generator_nonzero C.labels σ hG (Subtype.ext h)

private lemma real_traceless {J:(Bel C.book).Stress} (h:traceless E J) (hr : UVNext.FreeStress.pulsed H J=J) : ∃ x : ℂ,J = x • T0:= by
   obtain ⟨a,d,p,Ht⟩:= Trace.decomposed_stress H E (Maxwell.Free.gear_laws C.labels) (Maxwell.Free.gear_motion C.labels)
       (single (C:=C) hG).tensor hG h.tensor h.sym fun i j=> congr_fun (congr_fun hr i) j
   let w:= d • Trace.scalarLabel C.labels + p • ((S').unit 4)
   have hw: w=0 := by
       have hz : ∑ i:Axis,J i i=0:= h.trace
       simp only [Ht,if_true,Finset.sum_add_distrib] at hz -- expands extra? fix
       have v:=single (C:=C) hG |>.trace
       rw [← Finset.smul_sum,v,smul_zero,zero_add] at hz
       have hw : (4:ℂ) • w=0:=by
          simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin] at hz; unfold w
          simp_rw [← Nat.cast_smul_eq_nsmul ℂ] at hz; push_cast at hz; rw [smul_add]; exact hz
       exact (smul_eq_zero.mp hw).resolve_left (by norm_num)
   refine ⟨↑a,funext fun i=>funext fun j=>?_⟩
   simp only [Ht]; change a • T0 i j+(if i=j then w else 0)= (↑a:ℂ) • T0 i j
   simp [hw]
/-- Exact stress Schur equation on the **complex** representation. -/
lemma coversCrew {J:(Bel C.book).Stress} (h:traceless E J) : ∃ x:ℂ,J=x • T0:= by
   let W:=pulsed H J; let O:= J+W; let P:= Complex.I • (J-W)
   have hW : traceless E W:= h.reflect H (Maxwell.Free.gear_laws C.labels)
   obtain ⟨p,hp⟩:= real_traceless hG (h.add hW) (by
      unfold W; unfold pulsed; funext i j; simp only [Pi.add_apply,map_add]; rw [ (S').reflect_star ]; exact add_comm ..)
   obtain ⟨q,hq⟩:= real_traceless hG ((h.remove hW).scale Complex.I) (by
     unfold W; unfold pulsed; funext i j; simp only [Pi.smul_apply, Pi.sub_apply, map_smulₛₗ,map_sub]
     rw [(S').reflect_star]; simp [smul_sub]; abel )
   change P=q • T0 at hq; change O=p • T0 at hp
   refine ⟨(p-Complex.I*q)/2,?_⟩
   calc
     J = ((1/2:ℂ) • (O-Complex.I • P)):=by
           unfold O P; rw [smul_smul,Complex.I_mul_I,neg_one_smul]
           module
     _ = _ := by rw [hp,hq]; module
end base
end YM.SharpGram.Load
