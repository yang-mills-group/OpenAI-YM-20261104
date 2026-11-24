import YM.Frontier6.Bouquet.Atlas.Unity

/-! Current radius geometric support on the Court. In the common coordinates
 the child's relative atoms don't have to be uniformly separated from their own
 centroid, but stay in these cradles of occupancy before projection. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Metric Submodule
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P Q: Ensemble}{i:P}{x:Seats P}
namespace Court
variable (Z:Court i)
def place (x: Seats P)(r:ℝ) (p:Z.split) := closedBall (r • Z.root p + x i) (r*Z.radius)
def met (r:ℝ) (u:fiber P): Prop:= r⁻¹ • rune i u∈Z.chamber
def Contains (r:ℝ) (f:Full (fiber P)): Prop:= ∀ v∈ tsupport f, Z.met r v
section
variable {r:ℝ}(hr:0<r){u:fiber P}(h:Z.met r u)
include hr in
lemma slide (p:Z.split)(hp:p∈ Z.small){j:Slot}(hj:j∈ p.val.val) : r • (house j (r⁻¹ • rune i u).val)=house j u.val :=by
   rw [Submodule.coe_smul, map_smul, smul_inv_smul₀ hr.ne']; exact (begins i u j ((members' ..).mp hp hj)).symm
include h hr
lemma situate (p:Z.split)(hp:p∈Z.small){j:Slot}(hj:j∈p.val.val): actual x u i j∈ Z.place x r p:=by
   apply ball_subset_closedBall;
   have hf:= h p hp j hj; unfold actual; rw [mem_ball] at *; rw [← Z.slide hr p hp hj]; rw [dist_add_right,dist_smul₀]; rw [Real.norm_of_nonneg hr.le]; exact mul_lt_mul_of_pos_left hf hr
omit h
lemma scene_gap (x: Seats P){p q:Z.split}(he:p∈Z.small)(hv:q∈Z.small)(hp:p≠q){u v:E4}(hu:u∈ Z.place x r p)(hw:v∈ Z.place x r q): Z.clearance * r ≤ ‖u-v‖:=by
    let a(p:Z.split):= r • Z.root p + x i; have h1:dist (a p) (a q) ≤ (dist u (a p)+dist u v)+dist v (a q):=by rw [dist_comm u (a p)]; exact (dist_triangle _ v _).trans (add_le_add (dist_triangle _ u _) le_rfl)
    have h2: dist (a p) (a q) =r * dist (Z.root p) (Z.root q):=by unfold a; rw [dist_add_right,dist_smul₀,Real.norm_of_nonneg hr.le]
    have h3:dist u (a p) ≤ r*Z.radius:=hu; have h4:dist v (a q) ≤ r*Z.radius:= hw; rw [h2] at h1; rw [←dist_eq_norm]; nlinarith only [h1,h3,h4, mul_le_mul_of_nonneg_left (Z.gap p he q hv hp) hr.le]
include h
lemma opening {p q:Z.split}(he:p∈ Z.small)(hv:q∈Z.small) (hp:p≠q){a b:Slot}(ha:a∈ p.val.val)(hb:b∈q.val.val) : Z.clearance*r ≤ ‖house a u.val-house b u.val‖:=by simpa only [actual, Pi.zero_apply,add_zero] using Z.scene_gap hr 0 he hv hp (Z.situate (x:=0) hr h p he ha) (Z.situate (x:=0) hr h q hv hb)
-- pay separation in active branch and all witnesses crossing
omit h hr in
lemma focus (p q:Z.split)(hh:assign Z.legend.le p= assign Z.legend.le q)(hr:p≠q):p∈ Z.small ∧ q∈ Z.small:=by
    by_cases hv:assign Z.legend.le q=i; exact ⟨(members ..).mpr (hh.trans hv),(members ..).mpr hv⟩
    exact (hr ((Z.legend.same_pod hh hv).trans (Z.legend.same_pod (u:=q) rfl hv).symm)).elim
lemma separates : Separate Z.legend.le u:=by
    intro p q hv he z w hx hy hu; obtain ⟨hp,hq⟩:= Z.focus p q he hv; have ht:= Z.opening hr h hp hq hv hx hy; rw [hu,sub_self,norm_zero] at ht; exact not_le.mpr (mul_pos Z.pos hr) ht
omit h hr in
lemma scar (p:Pod)(hp:p∈ scars P Z.split): p ≤ i.val:=by
   obtain ⟨q,hq,he⟩:= encloses.mp (Finset.mem_sdiff.mp hp).1; by_cases hv:q=i.val; exact hv ▸ he; have hh:= Z.legend.holds ⟨_,hq⟩ (fun H=>hv (congr_arg Subtype.val H)); exact False.elim ((Finset.mem_sdiff.mp hp).2 (encloses.mpr ⟨q,hh,he⟩))
omit h hr in
lemma scar_pair (p: Pod)(hp:p∈ scars P Z.split): ∃ (j k:Z.split)(a b:Slot), j∈Z.small ∧ k∈ Z.small ∧ j≠k∧ a∈p.val∧ a∈j.val.val∧ b∈p.val ∧ b∈ k.val.val:= by
    let Q:=Z.split; have h': p ≤ i.val:= Z.scar p hp
    have hV(a:Slot)(ha:a∈p.val): a∈ Q.Along:= ref_slots Z.legend.le ▸ listed _ _ i.property (h' ha); let f(a:p.val):= owner Q ⟨_,hV a a.property⟩; have hx(a:p.val):a.val ∈ (f a).val.val:= belongs ..; have hg(a:p.val): f a∈ Z.small:= (members' ..).mpr (not_cross Z.legend.le (f a).property i.property (hx a) (h' a.property));
    let a:p.val:=⟨_,p.here_mem⟩; by_contra ht; apply (Finset.mem_sdiff.mp hp).2; apply encloses.mpr; refine ⟨(f a).val,(f a).property,fun b hb=>?_⟩; let c:p.val:=⟨b,hb⟩; have he:f a=f c:=by_contra fun h=> ht ⟨_,_,a,c,hg a,hg c,h,a.property,hx a,c.property,hx c⟩; exact he ▸ hx c
lemma sensitive (p:Pod)(hp:p∈ scars P Z.split):Z.clearance*r ≤ 2* ‖ontoSpace (normal p) u.val‖:=by obtain ⟨j,k,a,b,hj,hk,H,hp₁,ha,hp₂,hb⟩:=Z.scar_pair p hp; exact le_trans (Z.opening hr h hj hk H ha hb) (normGap hp₁ hp₂);
end
end Court
end YM.Frontier6.Bouquet.Atelier
