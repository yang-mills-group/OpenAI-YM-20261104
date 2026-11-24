import YM.OPE.Compatible.Minuet.Chart
/-!
 # held illumination on all spellings. tall-loop ledger.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open AnalyticBridge.VerifiedReset
open Next.Rank.Thirst
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : Rep G f}
    {p : BudgetPoint} {m n: ℕ} {W a r t σ E Λ μ x κ C w ε D b B: ℝ} {Ñ:ChartRatio G}
variable {F:Forest S.ratio} {I J:Seats F}{X Y Z:Support f}{q:Support c}
lemma crust (h:Primacy F I J Y X Z q R.p.B n) :FoldsGrip F I X:=by
   have hv : chairMap F I ⊆ chairMap F J := Finset.image_subset_image h.nested
   have he (X Y:Support f) (ht:X⊆Y):RG.inspected X⊆RG.inspected Y:=by
      intro j hj; rcases mem_union.mp hj with hh|hh; exact mem_union_left _ (ht hh)
      obtain ⟨x,hx,hp⟩:= mem_biUnion.mp hh; split at hp; swap
      · rename_i hg; refine mem_union_right _ (mem_biUnion.mpr ⟨x,hx,?_⟩); rw [if_neg (fun H=> hg (Disjoint.mono_left ht H))];exact hp
      simp at hp
   refine ⟨h.broad.present,fun i hi=>h.broad.sites i (hv hi),?_⟩
   exact (he _ _ (he _ _ (Finset.image_subset_image hv))).trans h.broad.flags
-- exposure limit in prob.Hand
abbrev lights (J:Seats F)(U:F.Slice G)(t:ℝ): Prop:= ∀ i∈J,G.chord (U i) ≤ t
lemma shutterCh (P: Face (Per f)) (U:Config G f)(t:ℝ)(hp:∀ i:Bond f,i.1 ∈ RG.touched P → (i.1+step i.2)∈ RG.touched P→ G.chord (U i)≤ t): G.chord (faceValue U P) ≤ 4*t:=by
   have hv(x:Site f)(w:Walk) (h:∀ i:Bond f,i.1 ∈ (Lattice.visits x w).toFinset → (i.1+step i.2)∈ (Lattice.visits x w).toFinset→G.chord (U i)≤ t): G.chord (travel U x w) ≤ w.length*t:=by
      induction w generalizing x with
      | nil=> simp [travel]
      | cons d w ih=>
        let y:= x+d.vec; have hj : (Lattice.visits y w).toFinset⊆(Lattice.visits x (d::w)).toFinset:=by simp only [Lattice.visits,List.toFinset_cons]; exact subset_insert ..
        have hx':x∈ (Lattice.visits x (d::w)).toFinset:=by simp [Lattice.visits];
        have hx:y∈ (Lattice.visits x (d::w)).toFinset:= hj (by cases w <;> simp [Lattice.visits]);
        have he : G.chord (d.read U x)≤t:=by
          rcases d with ⟨i,a⟩; unfold y Step.vec at *; cases a
          · exact h (x,i) hx' (by simpa using hx)
          · simp only [Step.read, ↓reduceIte,G.chord_inv]; exact h _ (by simpa [Step.used,sub_eq_add_neg] using hx) (by simpa [Step.used] using hx')
        rw [travel]; apply (G.chord_triangle ..).trans; apply (add_le_add he (ih y (fun i h1 h2=> h _ (hj h1) (hj h2)))).trans_eq; rw [List.length_cons]; push_cast; ring
   exact (hv _ _ hp).trans (by unfold square; norm_num)
namespace Primacy
variable (V:Primacy F I J Y X Z q R.p.B n) (U:F.Slice G)
include V
lemma grub (hf:0≤r)(ht:4*r ≤ R.p.threshold) (h : lights J U r): Healthy R.p.threshold Y (F.drape U):=by
   refine Finset.disjoint_left.mpr fun i hi hj=> ?_
   obtain ⟨p,hp,he⟩:= (RG.flags_spec ..).1 hj
   exact not_le.mpr he ((shutterCh p (F.drape U) r fun u hu _=> by
     by_cases hv:u∈F.trunks
     · rw [F.on_tree U ⟨u,hv⟩]; rwa [G.chord_one]
     let j:F.Free:=⟨u,hv⟩; rw [show F.drape U u=_ from F.off_tree U j]; apply h; refine V.flagged j (Finset.mem_union_right _ (mem_biUnion.mpr ⟨p,mem_univ _,?_⟩)); rw [if_neg]; exact hu; exact Finset.not_disjoint_iff.mpr ⟨i,hi,hp⟩).trans ht)
omit V in
lemma glints (hf:0≤r)(h:lights J U r): lights J (shave I U) r:=by
   intro i hi; unfold shave; split
   · rw [G.chord_one];exact hf
   exact h i hi
lemma kite (hf:0≤r)(hL:lights J U r): naked S q n (F.drape U) r:=by
    intro i hi; by_cases he:i∈F.trunks
    · rw [F.on_tree U ⟨i,he⟩]; rwa [G.chord_one]
    let j:F.Free:= ⟨i,he⟩; rw [show F.drape U i= _ from F.off_tree U j]; exact hL j (V.modest _ (halo_mono (le_max_left n (predReach S.patch+1)) le_rfl hi))
variable (H:S.patch.Branches S.kernel G) (h:R.Lawful σ C Λ E w)(hc:WilsonStartup.Decent R.clip R.p)(hy:Geo.Width R.p R.clip σ)
 (hk:m ≤ R.p.B)(W:Config G c)(k:S.Choices)(u:F.Slice G)(t:F.Slice G) (ha:0≤ B)(hb:4*B≤ R.p.threshold)
include H h hc hy hk ha hb
lemma linked (he:curveF F J u=curveF F J t)(hx:lights J u B)(hT:lights J t B): Ruin R W m I k (F.drape u)=Ruin R W m I k (F.drape t):=by
   have hs(z:F.Slice G)(hz:lights J z B):Healthy R.p.threshold Y (F.drape z) ∧ Healthy R.p.threshold Y (razed I (F.drape z)):= ⟨V.grub _ ha hb hz,by rw [draped]; exact V.grub _ ha hb (glints z ha hz)⟩
   have hp := spatial h hc hy V.small V.supports hk (F.drape u) (F.drape t) (agrees_mono (stroll u t he _ V.flagged) (Finset.coe_subset.mpr (show Y ⊆ RG.inspected Y from subset_union_left))) (hs u hx).1 (hs u hx).2 (hs t hT).1 (hs t hT).2
   unfold Ruin; rw [hp,V.m_angle H u t he k W]
variable (hu:∀ U:Config G f,naked S q n U B→ ordFrame S (halo 1 q) U ∧ ordBest S q U)
include hu
lemma soma (hp:lights J u B) :
    S.density R.beta (F.drape u) W*mellow R X (F.drape u)*Real.exp (cinnamon R m I (F.drape u))= S.density R.beta (F.drape (shave I u)) W*mellow R X (F.drape (shave I u))*Ruin R W m I k (F.drape u):=by
    have hj:lights J (shave I u) B:= glints u ha hp
    have hb' : naked S q n (razed I (F.drape u)) B := by rw [draped]; exact V.kite _ ha hj
    have ht:=hu _ (V.kite _ ha hp); have hv:=hu _ hb'; rw [← draped]; exact tallyW H h hc hy (crust V) V.small V.supports hk W _ (V.grub _ ha hb hp) (by rw [draped]; exact V.grub _ ha hb hj) q (V.travels _) ht.1 hv.1 ht.2 hv.2 k
end Primacy
end YM.PhysicalNext.Repeat.Aroma
