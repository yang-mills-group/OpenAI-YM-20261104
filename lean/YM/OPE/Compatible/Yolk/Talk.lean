import YM.OPE.Compatible.Basil.Offer
import YM.Planned.ATOM_GUARDED_LAYOUT.Guards
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Sails
/-!
 # Touch credits, even for long values. Distinguished site and support may be larger. Keeper compacts an entire exterior correction into the SAME vacuum. Adapt Leaf.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C s : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
structure Paced (R:Rep G f)(Z:Support f)(S:StepData c f)(h : Config G f→ℝ) (c:ℝ) : Prop where
   owns : UsesFinal R.p.threshold Z h
   meas : Measurable h
   pedal : Pedal S h
   bound : ∀ U, ‖h U‖ ≤ c
variable {X Y Z:Support f}
abbrev towY (A:Activities G f) (X:Support f)(i:Finset ℕ):= i.filter (fun j => ¬Disjoint (A.forced j).support X)
abbrev enrolY (A:Activities G f)(X:Support f)(i:Finset ℕ) := X ∪ i.biUnion (fun j=> (A.forced j).support)
abbrev groupY (A:Activities G f)(i:Finset ℕ) := i.biUnion (fun j=> (A.forced j).inventory)
abbrev Anchor (A:Activities G f) (X Y:Support f)(i:Finset ℕ) := (towY A X i).Nonempty ∧ towY A Y i = i
abbrev court (R:Rep G f)(Y:Support f)(i:Finset ℕ)(h:Config G f→ℝ)(U:Config G f):=if (i:Set ℕ).PairwiseDisjoint (fun j=> (R.activities.forced j).support) ∧ (enrolY R.activities Y i) ∩ RG.flags R.p.threshold U=groupY R.activities i then h U*∏ j∈i,R.activities.K j U else 0
def Crop (R:Rep G f)(i:ℕ)(v:ℝ) :=0≤v ∧ ∀ U,‖R.activities.K i U‖ ≤ v
variable (K:Keeper R.p R.activities){i:Finset ℕ}{h:Config G f→ℝ}{v:ℝ}{b:ℕ→ℝ}
include K
lemma give_slot (he:i.Nonempty) : ∃ k:ℕ,(R.activities.forced k).support=enrolY R.activities Y i ∧ (R.activities.forced k).inventory=groupY R.activities i ∧
  ∀ U,(enrolY R.activities Y i) ∩ RG.flags R.p.threshold U=groupY R.activities i → (R.activities.forced k).eligible R.p.threshold U:=by
   let X:= enrolY R.activities Y i; let y:= groupY R.activities i
   have hz:y ⊆ X:= fun p hp=>by
      obtain ⟨j,hj,hp⟩:=mem_biUnion.mp hp;exact mem_union_right _ (mem_biUnion.mpr ⟨j,hj,(R.activities.forced j).inventory_sup hp⟩)
   have hv:y.Nonempty:=by
      obtain ⟨p,hp⟩:=he; exact ((R.activities.forced p).inventory_ne).mono (subset_biUnion_of_mem _ hp)
   let q : Push.Local.Dummy f:=⟨⟨(X,y),hv,hz⟩,0⟩
   refine ⟨K.code q,K.support q,K.inventory q, fun U h=> ?_⟩
   have hb : ((R.activities.forced (K.code q)).support ∩ RG.flags R.p.threshold U)=(R.activities.forced (K.code q)).inventory:=by rw [K.support,K.inventory]; exact h
   exact ⟨hb,K.pass q U hb⟩
include K
lemma plays_Y (he:i.Nonempty) (hp : Paced R Y S h v) (hb:∀ j,Crop R j (b j)) (hl:R.activities.Valid R.p σ w):
 ∃ M:Leaf S R, ∃ k:ℕ, M.turn=Aroma.Wing.gasKey k ∧ (R.activities.forced k).support=enrolY R.activities Y i ∧
    (R.activities.forced k).inventory=groupY R.activities i ∧ M.weight=v*∏ j∈i,b j ∧ M.ingredient=court R Y i h:=by
   obtain ⟨k,h₁,h₂,h₃⟩:= give_slot (Y:=Y) K he
   let X:=enrolY R.activities Y i; let M:=(i:Set ℕ).PairwiseDisjoint (fun j=> (R.activities.forced j).support)
   let u:= court R Y i h
   have hv:0≤v:=(norm_nonneg _).trans (hp.bound 1)
   have hf (U): ‖u U‖ ≤ v*∏ j∈i,b j:=by
     unfold u court; split
     next he=> rw [norm_mul,norm_prod]; exact mul_le_mul (hp.bound _) (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=> (hb j).2 U)) (Finset.prod_nonneg fun _ _=> norm_nonneg _) hv
     next=> rw [norm_zero]; exact mul_nonneg hv (prod_nonneg fun i _=> (hb i).1)
   have hs : UsesFinal R.p.threshold X u :=by
      intro U V ht hV; unfold u court; rw [hV]; split
      next hv=>
        rw [hp.owns U V (agrees_mono ht (by exact_mod_cast (show Y ⊆ X from Finset.subset_union_left))) (by
          have hT : Y∩X=Y:=Finset.inter_eq_left.mpr (show Y⊆X from Finset.subset_union_left); rw [←hT,inter_assoc,hV,inter_assoc])]; apply congr_arg (_*·)
        exact Finset.prod_congr rfl fun j hj=> let hz: (R.activities.forced j).support ⊆ X:= (Finset.subset_biUnion_of_mem (fun j=> (R.activities.forced j).support) hj).trans Finset.subset_union_right; hl.forced.reads _ _ _ (agrees_mono ht (by exact_mod_cast hz)) (by
          rw [←Finset.inter_eq_left.mpr hz, inter_assoc,hV, inter_assoc])
      next=> rfl
   have hq : Measurable u:=by
     let g := groupY R.activities i; by_cases hi:M; swap; · change Measurable (fun U=> if M ∧ _ then _ else _); simp only [hi,false_and,↓reduceIte]; exact measurable_const
     have hJ:MeasurableSet {U:Config G f| X∩ RG.flags R.p.threshold U=g}:=by
       rw [show {U:Config G f| X∩ RG.flags R.p.threshold U=g}=⋃ k : {j:Support f// X ∩ j =g},{U|RG.flags R.p.threshold U=k.val} from ?_]; exact MeasurableSet.iUnion fun i=> flags_measurable_eq ..
       ext U; simp
     unfold u court; simp only [show (i:Set ℕ).PairwiseDisjoint (fun j=> (R.activities.forced j).support) from hi,true_and]; exact Measurable.ite hJ (hp.meas.mul (Finset.measurable_fun_prod _ fun i _=> hl.forced.meas _)) measurable_const
   have hG:Pedal S u:=by
     intro k hv U; unfold u court; rw [RG.gauge_flags]; split
     next h=> rw [hp.pedal k hv U]; apply congr_arg (_*·); exact prod_congr rfl fun j _=> hl.forced.sym _ k U
     next h=>rfl
   have ha:∀ U,u U≠0→ (R.activities.forced k).eligible R.p.threshold U:=by
     intro U he; unfold u court at he; split at he
     next h=> exact h₃ _ h.2
     next h=> exact (he rfl).elim
   exact ⟨⟨Aroma.Wing.gasKey k,u,(show UsesFinal _ (R.activities.forced k).support u from h₁.symm ▸ hs),ha,trivial,_,hf,hG,hq⟩,k,rfl,h₁,h₂,rfl,rfl⟩
end YM.PhysicalNext.Repeat.Aroma
