import YM.OPE.Compatible.Grout.Throat
/-!
 # Embedded block mask covariant region edit. Prepare Y. Reweight increments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
variable (F : Forest S.ratio) (I : Support f)
-- I any subset of free. persist sets
abbrev Seats (F:Forest S.ratio):= Finset F.Free
def chairMap (F:Forest S.ratio)(J:Seats F): Finset (Bond f):= J.image (fun p=>p.val)
variable {F} (J:Seats F)
def razed (U:Config G f):Config G f := fun e=> if e∈ chairMap F J then (F.foldAt U e.1)⁻¹ * F.foldAt U (e.1+step e.2) else U e
lemma root_z (U:Config G f)(j): (F.foldAt (razed J U)) j= F.foldAt U j:= by
    apply congr_fun (F.names _ U (fun i hi=> if_neg fun h=>by obtain ⟨p,hp,h⟩:= mem_image.mp h; exact p.property (h.symm ▸ hi)))
@[fun_prop] lemma steadyR : Measurable (razed (G:=G) J):= by
    apply measurable_pi_lambda; intro i; unfold razed; split_ifs <;> fun_prop
lemma stableR (U:Config G f) (k:Site f→G.El) (h:∀ i,k (S.ratio.embed i)=1): razed J (gauge k U)= gauge k (razed J U):=by
    have hz(x): F.foldAt (gauge k U) x=F.foldAt U x*(k x)⁻¹:=by unfold Forest.foldAt; rw [travel_gauge,F.hike_root,h]; group
    ext1 i; unfold razed; split
    next h=>
      rw [hz,hz]; change _ = k i.1 * razed J U i * (k (i.1+step i.2))⁻¹; unfold razed; rw [if_pos h]; group
    next h=>
      change _ = k i.1 * razed J U i * _; unfold razed; rw [if_neg h]; rfl
-- Two supports starting common X, require any flag face that can change ALL endpoint/inventory read through X including new q values vs ext.
def chairFoot (i:Finset (Bond f)) := i.image (fun x=>x.1)
structure FoldsGrip (F:Tree.Forest S.ratio)(J:Seats F)(X : Support f):Prop where
   present : X.Nonempty
   sites i : i∈ chairMap F J→ walksAt F i⊆ X
   flags : let A:Support f:= chairFoot (chairMap F J); RG.inspected (RG.inspected A) ⊆ X -- chairFoot define

section
variable {X Z Y:Support f}{J:Seats F}(h:FoldsGrip F J X)
include h
omit h in
lemma touches_fold (U:Config G f)(p : Face (Per f))(hF:faceValue (razed J U) p ≠ faceValue U p):RG.touched p⊆RG.inspected (chairFoot (chairMap F J)):=by
    suffices h₁ : ¬ Disjoint (chairFoot (chairMap F J)) (RG.touched p) by
      intro j hj; exact mem_union_right _ (Finset.mem_biUnion.mpr ⟨p,mem_univ _,(by rw [if_neg h₁]; exact hj)⟩)
    intro hx; apply hF; refine travel_local _ _ _ _ ?_; intro i hi _
    refine if_neg fun he=>Finset.disjoint_left.mp hx (mem_image_of_mem _ he) (List.mem_toFinset.mpr hi)
-- Read stencil X.Prop cert and unaffected. 
lemma edits_agrees (U V:Config G f)(ht:Agrees (↑(X∪Y):Set _) U V) : Agrees (↑(X∪ Y):Set _) (razed J U) (razed J V) :=by
   intro i hi ht'; unfold razed; split_ifs
   next hp=>
     have hx : Agrees (↑(walksAt F i)) U V:= agrees_mono ht (by exact_mod_cast ((h.sites _ hp).trans Finset.subset_union_left:walksAt F i⊆ X∪Y))
     unfold Forest.foldAt; rw [show travel U i.1 _ = travel V i.1 (F.hike i.1) from travel_local _ _ U V (agrees_mono hx (fun j hj=>mem_union_left _ (List.mem_toFinset.mpr hj))), show travel U _ _= travel V (i.1+step i.2) (F.hike _) from travel_local _ _ U V (agrees_mono hx (fun j hj=> mem_union_right _ (List.mem_toFinset.mpr hj)))]
   exact ht i hi ht'
omit h in
lemma edits_flags (U:Config G f)(x : Site f)(hx:x ∉ RG.inspected (chairFoot (chairMap F J)))(p:ℝ) : x∈ RG.flags p (razed J U) ↔ x∈ RG.flags p U:=by
    simp_rw [RG.flags_spec]; apply exists_congr; intro i; refine and_congr_right fun hi=>?_ ; rw [show faceValue (razed J U) i=faceValue U i from by by_contra he;exact hx (touches_fold U i he hi)]
lemma amended (U V:Config G f)(ht:Agrees (↑(X∪Y):Set _) U V)(p:ℝ)(hs:(X∪Y) ∩ RG.flags p U=(X∪Y)∩RG.flags p V) : (X∪Y)∩RG.flags p (razed J U)=(X∪Y)∩RG.flags p (razed J V):=by
   have he := flags_agree p (razed J U) (razed J V) (RG.inspected (chairFoot (chairMap F J))) (agrees_mono (edits_agrees h U V ht) (by exact_mod_cast (h.flags.trans subset_union_left: _ ⊆X∪Y)))
   ext z; simp only [mem_inter]; apply and_congr_right; intro hz
   have hx : z∈ RG.flags p U↔ z∈RG.flags p V:= by simpa only [mem_inter,hz,true_and] using (Finset.ext_iff.mp hs z)
   by_cases hp : z∈ RG.inspected (chairFoot (chairMap F J)); · simpa only [mem_inter,hp,true_and] using (Finset.ext_iff.mp he z)
   rw [edits_flags U z hp p,hx,edits_flags V z hp]
def tweak (J:Seats F) (u:Config G f→ℝ) U := u U-u (razed J U)
lemma majesty {K:ℝ}{u:Config G f→ℝ} (hp:Paced R Z S u K) : Paced R (X ∪ Z) S (tweak J u) (2*K):=by
   have hf:=hp.rise (X:=Z) (Y:=X∪Z) Finset.subset_union_right le_rfl
   refine ⟨fun U V hx hV=> congr_arg₂ (·-·) (hf.owns U V hx hV) (hf.owns _ _ (edits_agrees h U V hx) (amended h U V hx _ hV)),hp.meas.sub (hp.meas.comp (steadyR J)), ?_,?_⟩
   · intro k hv U; unfold tweak; rw [stableR _ _ _ hv,hp.pedal k hv,hp.pedal k hv]
   intro U; exact (norm_sub_le _ _).trans ((add_le_add (hp.bound _) (hp.bound _)).trans_eq (two_mul _).symm)
lemma struckNear {K:ℝ}{u:Config G f→ℝ}(hp:Paced R Z S u K)(hz:tweak J u ≠ 0): ¬ Disjoint X Z:=by
   intro he; apply hz; funext U; change u U-_=0; refine sub_eq_zero.mpr (hp.owns U _ (fun i hi _=> Eq.symm (show razed J U i=U i from ?_)) ?_)
   · refine if_neg fun hz=>Finset.disjoint_left.mp he (h.sites _ hz (costPose F i).1) hi
   ext z; simp only [mem_inter]; apply and_congr_right; intro hx; apply Iff.symm; apply edits_flags; intro hz; exact Finset.disjoint_left.mp he (h.flags (mem_union_left _ hz)) hx
lemma trouble {K:ℝ}{u:Config G f→ℝ}(hp:Paced R Z S u K)(hz:tweak J u ≠ 0): PaidY R S X (coverNumber R.p.B Z) (tweak J u) (2*K):=by
   obtain ⟨j,hj,hd⟩:=Finset.not_disjoint_iff.mp (struckNear h hp hz)
   refine ⟨X∪Z,subset_union_left,majesty h hp,fun y hy=>?_⟩; rw [← union_assoc, Finset.union_eq_left.mpr hy]; exact meets_sum (hy hj) hd _
end
end YM.PhysicalNext.Repeat.Aroma
