import YM.RegulatorIR.Binding.Laps

/-! Forest chart, additive pins for relative directions, plus global terminal
chart. Null coherence both senses. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Geometry.End Geometry.Field Geometry.Bark Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Precision Tree Tree.Forest
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical Matrix.Norms.Frobenius
variable {f c: Side}{G:Gauge}
variable (S:StepData c f) (H:S.patch.Branches S.kernel G)
variable {F:Forest S.ratio} (Q: Geometry.Field.Square F) (hf:Even f.val)(hc:Even c.val)
lemma pinG (F:Forest S.ratio) : cloth (G:=G) F 1=1:=by
 ext1 i; by_cases h:branch F i
 · exact cloth_far F _ ⟨i,h⟩
 exact cloth_at F _ ⟨i,h⟩

def Flat (G:Gauge)(f : Side)(U:spins G f) : Prop:= ∃ k:Site f→ G.El,compatible k ∧ goat k U=1
include H
lemma glide (U: spins G f)(h:Flat G f U): Flat G c (predictor S U):=by
 obtain ⟨k,hk,hu⟩:=h; exact ⟨k ∘ S.ratio.embed, restrict_site (g:=S.ratio) hk,by rw [← prediction_flow S H U k hk,hu,predict_zero S H]⟩
lemma glass (U:spins G f)(h:Flat G f U): ContinuousAt (predictor S) U:=by obtain ⟨k,hk,he⟩:=h; exact look_flat S H U k hk he
include Q
lemma fiber_flat (x: Wind F→ G.El)(h:Flat G f (cloth F x))(hh: predictor S (cloth F x)=1): x=1:=by
 obtain ⟨k,hk,hv⟩:=h
 let ef:=S.ratio.embed;let u:Site c→G.El:= k ∘ ef
 have hU : goat u 1=1:=by rw (occs:=.pos [1]) [← hh]; rw [← prediction_flow S H _ _ hk,hv,predict_zero S H]
 let hg:Site f→G.El:= fun _=>(u 0)⁻¹
 have he:(1:spins G _)=goat (hg*k) (cloth F x):= by rw [← goat_pair,hv];ext1 i; rw [goat_at];simp [hg]
 have hp:cloth F x=1:=by
    refine Geometry.rooted_eq Q (mul_comp (u:=hg) (fun _=>rfl) hk) he (fun i=>?_) (cloth_far F x) (fun _=>rfl)
    change (u 0)⁻¹*u i=1; rw [gauge_base_neutral u (restrict_site hk) hU i,inv_mul_cancel]
 funext i
 exact (cloth_at F x i).symm.trans (congr_fun hp i.val)
-- include helpers

-- restrict coordinates to Wind & extend by zero trunks
omit Q H
variable {S Q hf hc}

def injectX (F:Forest S.ratio) : Meadow G (Wind F)→ₗ[ℝ] Horizon G f where
 toFun x i := if h: ¬Geometry.Field.branch F i then x ⟨i,h⟩ else 0
 map_add' x y:= by ext1 i; rw [Pi.add_apply];split_ifs <;> simp
 map_smul' t u:=by ext1 i; rw [Pi.smul_apply];split_ifs <;> simp
lemma inject_access (F:Forest S.ratio)(x:Meadow G (Wind F))(i:Wind F): injectX F x i.val=x i:=by unfold injectX; simp [i.property]
lemma inject_others (F: Forest S.ratio)(x:Meadow G (Wind F))(i:Knot F): injectX F x i.val=0:=by unfold injectX; simp [i.property]
lemma chart_commute (F:Forest S.ratio)(x:Meadow G (Wind F)): cloth F (Chart.expLinks G _ x)= climb (injectX F x):=by
 ext1 i; change _=G.lieExp _; by_cases h:branch F i
 · rw [show cloth F _ i=1 from cloth_far F _ ⟨i,h⟩,show injectX F _ i=0 from inject_others F x ⟨i,h⟩, G.mat_lieExp_zero]
 rw [show injectX F x i=x ⟨i,h⟩ from inject_access F x ⟨i,h⟩]; exact cloth_at F _ ⟨i,h⟩

include Q H
lemma fiber_core (x: Meadow G (Wind F))(h:GradientSite (injectX F x))(he:Even f.val)(he': Even c.val)(ht:rod G S (injectX F x)=0): x=0:=by
 obtain ⟨k,hk,hv⟩:=h
 let u:Site c→ G.Color:= k∘ S.ratio.embed;rw [hv,slopes S H k hk] at ht
 have hU i : u i=u 0:=by
    apply gradie_still u ?_ he' ht i
    intro i; change k (S.ratio.embed (-i))= _; rw [show S.ratio.embed (-i)= -S.ratio.embed i from S.ratio.root.map_neg i, hk]; rfl
 have hh (v : Site f) : k v = k (S.ratio.embed (S.ratio.parent v)):=by
    induction v using Forest.hike.induct F with
    | case1 i hi ih=>
       rw [F.stays i hi] at ih
       apply Eq.trans _ ih
       apply sub_eq_zero.mp
       rw [← pays_gradient k hk he (F.up i) i, ←hv]
       have he : branch F (index ((F.up i).used i)):= (bone Q _).mpr ((F.trunk_mem_iff _).mpr ⟨i,hi,rfl⟩)
       unfold cash fire; simp only [show injectX F x (index ((F.up i).used i))=0 from inject_others F x ⟨_,he⟩];split_ifs <;> simp
    | case2 i hi=>exact congr_arg k (Classical.not_not.mp hi)
 have hp (i): k i= u 0:=(hh i).trans (hU (S.ratio.parent i))
 funext i
 exact (inject_access F x i).symm.trans (show injectX F x i.val=0 from by rw [hv,gradie, hp,hp,sub_self])
end YM.RegulatorIR.Binding
