import YM.OPE.Vitrines.Left
import YM.OPE.Loom.Prices
/-!
# Membrane geometry and qualifications
- The F proxy is a TAIL over whole labels and its entire support fits.Flex painted.
Only translations needed for now.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Vitrines
open Lattice Wilson RG Function Filter Set MeasureTheory Marker Push
open MergeProof Accent Ribbons ManyCopies Patrol MergeProof.Float Source Labels Extra.Histories Next Next.UVStress
open Extra.Multi Planned.GuardedAtom Local PhysicalNext.Repeat Lotus Motion Therm.House Therm.Portolan Cells
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{d:ℕ}{n:Side}{σ C Λ δ w ρ θ:ℝ}
variable {D:Labels.Frame G d}(S:SectionData D){R:Rep G n}{P:Coefficient D n}
local notation "𝒞"=> Config G n
local notation "x₀"=> (0:Site n)
local notation "t"=> R.p.threshold
local notation "B"=> R.p.B
local notation "X"=> P.support
lemma near_form (he:P.remBound x₀ R ρ C)(r:ℕ)(v:𝒞): enamel S R P r v= P.x 0 + masked t (S.footprint x₀) (S.places (D.scaled (t)⁻¹ (D.core P.x)) x₀) v+ ∑' i,(if height R P i<r then P.maskedTerm R i v else 0):=by
   let X' i:= P.maskedTerm R i v; let s i:= relict R P v i r; have hh:= P.regular_series he; have ht:Summable s:= by
       refine (((hh.summable v).indicator (s:={i|r≤height R P i}))).congr fun i=>?_; by_cases he: r≤height R P i <;> simp [relict,s,Set.indicator,he]
   unfold enamel Coefficient.exponentialEntry drift; rw [add_sub_assoc,← Summable.tsum_sub (hh.summable v) ht]; apply congr_arg; apply tsum_congr; intro i; unfold s relict; split_ifs<;>first|omega|abel
lemma enamel_local {Y:Hol G}(h:P.Format x₀ Y R)(hn:P.remBound x₀ R ρ C)(hS:S.Sound Y)(r:ℕ):
    Interior (halo (BasisCost.extent S+Therm.Stove.eroom R.p r) ({0}:Support n)) (enamel S R P r) :=by
    let p:=R.p; let v:=D.scaled p.threshold⁻¹ (D.core P.x); let F:= S.places v x₀; let X':= S.footprint x₀; let K:=BasisCost.extent S; let Y':= Fintype.card (Site n) -- junk
    let l(Y:Support n):= halo 8 Y
    let g:= masked t X' F; let u:= halo (K+Therm.Stove.eroom p r) ({0}:Support n); have he: l X' ⊆ u:=by
       intro x hx; obtain ⟨y,hy,hY⟩:= halo_spec.mp hx; obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hy; apply halo_spec.mpr; refine ⟨0,Finset.mem_singleton_self _, (separation_triangle _ (wrap n z+0) x).trans (le_trans (Nat.add_le_add (show separation x₀ _≤ K from ?_) hY) (Nat.add_le_add_left ?_ _))⟩
       · rw [separation_comm,separation,add_zero,sub_zero]; apply Finset.sup_le; intro i _; exact (Corona.lap z _).trans ((Finset.le_sup_of_le hz (Finset.le_sup (f:=fun i=>(z i).natAbs) (Finset.mem_univ i))) : (z i).natAbs ≤ K)
       unfold Therm.Stove.eroom; omega
    let s i v:= if height R P i<r then P.maskedTerm R i v else 0
    have hm: enamel S R P r=fun v=>P.x 0+g v+∑' i,s i v:= funext fun i=> near_form S hn _ i
    rw [hm]; have hT: Dominated (fun i v=>s i v):=by
       obtain ⟨f,hf,hg⟩:=P.regular_series hn; refine ⟨f,hf,fun i v=>?_⟩; unfold s; dsimp only; split; exact hg i v;rw [norm_zero]; exact (norm_nonneg _).trans (hg i v)
    obtain ⟨z,hz⟩:=hT.bound
    have hF: Envelope g:=by
       have hv:= Envelope.compactC (S.continuous_places v x₀); obtain ⟨c,H⟩:=hv.cost; refine ⟨masked_measurable _ _ _ hv.meas,c,fun U=>?_⟩; unfold g; by_cases h:Healthy t X' U; rw [masked_eq _ _ _ _ h]; exact H U; rw [masked_ne _ _ _ _ h,norm_zero]; exact (norm_nonneg _).trans (H U)
    obtain ⟨q,hq⟩:=hF.cost
    refine ⟨fun U V=>?_,(measurable_const.add hF.meas).add (Measurable.tsum (fun i=>?_)),fun U V H0=>?_,‖P.x 0‖+q+z,fun U=> (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add le_rfl (hq U))) (hz _))⟩
    · have he:g (gauge U V)=g V:= Rank.Alarm.sails _ _ _ (S.placed_invariant hS x₀ v) _ _; rw [he]; apply congr_arg; apply tsum_congr; intro i; unfold s; split; exact Rank.Alarm.sails _ _ _ ((h.smooth i).symmetry) _ _; rfl
    · unfold s; split; exact masked_measurable _ _ _ (h.smooth i).borel; exact measurable_const
    have hy:g U=g V:= Rank.Alarm.sail _ _ _ (S.placed_local x₀ v) U V (agrees_mono H0 (fun x hx=> he hx)); -- h shadow
    rw [hy]; apply congr_arg; apply tsum_congr; intro i; unfold s; split; swap; · rfl
    rename_i hv; apply Rank.Alarm.sail _ _ _ ((h.smooth i).sites) U V (agrees_mono H0 ?_); intro x hx; obtain ⟨y,hy,hP⟩:= halo_spec.mp hx; apply halo_spec.mpr; refine ⟨0,Finset.mem_singleton_self _, (separation_triangle _ y _).trans ?_⟩; have ht:= ((Corona.extent _ (B) (h.origin i) hy).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hv.le) _)); exact (Nat.add_le_add ht hP).trans (Nat.le_add_left ..)
local notation "a"=> ((1,false):Motion)
lemma conical {v:ℂ}{g:Config G n→ℂ}{K:MergeProof.Res G n}{C:ℝ}(x:Site n)(π:R.activities.Moves (1:Signed) x) (h:Blade R x₀ g K v C) : Blade R x (stepUp a x g) (floatUp a x K) v C:=by
   obtain ⟨I,i,M,s,h⟩:=h; let M' i:= Leaf.route π (M i); refine ⟨I,i,M',s,fun i=>?_,?_,?_,?_⟩
   · have hh:= Finset.mem_image_of_mem (turnSites (1:Signed) x) (h.sit i); rw [show (M' i).crest= _ from crestSky a _ π (M i),shading]; convert hh; exact (show affine 1 x 0=x from by simp [affine]).symm
   · rw [h.lit]; funext U; change v+(∑ i,s i • prose (M i)) (pull 1 x U)= v+(∑ i,s i • prose (M' i)) U; simp_rw [show ∀ i,prose (M' i) = _ from fun i=> climb_p a x π (M i),Finset.sum_apply,Pi.smul_apply]; rfl
   · rw [h.run]; funext p U; unfold floatUp; simp_rw [show ∀ i,entry (M' i)=_ from fun i=>climb_entry a _ π (M i), Finset.sum_apply,Pi.smul_apply]; unfold stepUp; rw [Finset.sum_apply]; rfl
   apply le_trans _ h.pay; unfold M'; simp_rw [fareSky a]; exact le_rfl
end YM.OPE.Vitrines

