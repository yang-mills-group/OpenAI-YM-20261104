import YM.MSbar.Sat.Probe
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{U W:Config G f}{V:Config G c}{R:Rep G f}{σ C T a v y δ w D b u t:ℝ}
open Finset
open YM.MSbar.Bulk SectorNext.Vacuum Precision Tree Pressure Pressure.Stores Push.Uniform
variable (F : Forest S.ratio) {Y Y' :Support f}
local notation "N"=>Config G f
-- guard around READ. radius in native fine sites.
def youth (F:Forest S.ratio) (Y:Support f): Support f:= halo (4*S.patch.L.val+8) Y
def excavation (F:Forest S.ratio) (Y:Support f) (t b : ℝ): Set (Config G f):= {U | Healthy t Y U ∧ ∀ i: F.Free, i.val.1∈Y → G.chord (canoe (S:=S) F U i.val) ≤ b}
set_option quotPrecheck false
local notation "L₀"=>S.patch.L.val
def attend (F:Forest S.ratio)(Y:Support f)(j:F.Free):=j.val.1∈Y
lemma catalog : inspected Y⊆ youth F Y:= (Next.Scheduling.flag_layer _).trans (Corona.halo_mono (show 8≤4*S.patch.L.val+8 by omega) subset_rfl)
lemma page {x:Site f} (hp:x∈halo 1 Y): (visits x (F.hike x)).toFinset ⊆ youth F Y:=by
    obtain ⟨i,hi,H⟩:= halo_spec.mp hp; intro j hj; have hl :=Push.AbsoluteSums.Paths.to_ball _ _ hj
    exact halo_spec.mpr ⟨i,hi,(separation_triangle _ _ _).trans ((Nat.add_le_add H (hl.trans ((F.hike_lower _).trans (F.bound _)))).trans (by omega : 1+4* S.patch.L.val≤_))⟩
lemma turnbook {U V:Config G f}(h:Agrees (youth F Y) U V) (e:Edge (Site f)) (he:e.1∈Y) : canoe (S:=S) F U e=canoe (S:=S) F V e:=by
   have hp (x:Site f)(hx:x∈halo 1 Y): F.foldAt U x= F.foldAt V x:= congr_arg Inv.inv (travel_local _ _ _ _ (agrees_mono h (fun i hi=> (page F hx (List.mem_toFinset.mpr hi)))))
   have ht : e.1+step e.2∈ halo 1 Y:=halo_spec.mpr ⟨_,he,Work.E01.sep_step_le ..⟩; have hi : U e=V e:= h e (halo_subset _ _ he) (Corona.halo_mono (show 1≤4* S.patch.L.val+8 by omega) subset_rfl ht)
   unfold canoe Lattice.gauge; rw [hp _ (halo_subset 1 _ he),hp _ ht,hi]
private lemma landed (t b:ℝ) (Y:Support f): MeasurableSet (excavation (G:=G) F Y t b):=by
    unfold excavation; simp only [Set.setOf_and,Set.setOf_forall]; apply MeasurableSet.inter (healthy_closed ..|>.measurableSet)
    refine MeasurableSet.iInter fun i=>MeasurableSet.iInter fun _=> ?_; exact (isClosed_le (G.continuous_chord.comp ((continuous_apply i.val).comp (canoe_cont ..))) continuous_const).measurableSet
lemma vital (Y: Support f)(t b:ℝ) : Seal S (youth F Y) (excavation (G:=G) F Y t b):=by
   refine ⟨landed F t b Y,fun i hv U=> ?_,fun U V he=>?_⟩
   · simp [excavation, Healthy,gauge_flags, grove F _ _ hv]
   apply propext; unfold excavation; simp only [Set.mem_setOf_eq]; apply and_congr; · unfold Healthy; rw [disjoint_iff_inter_eq_empty,flags_agree _ _ _ _ (agrees_mono he (coe_subset.mpr (catalog F))),disjoint_iff_inter_eq_empty]
   exact forall_congr' fun i=> forall_congr' fun hx=> by rw [turnbook F he i.val hx]
lemma shrinking (V:Config G c)(h:Admitted V R S σ C δ T w) {v y:ℝ}(t b:ℝ)(Y : Support f)
    (hv: ∀ i∈Y, chance S R V {U | i∈flags t U} ≤ y) (hC: ∀ i:F.Free, i.val.1∈Y → chance S R V {U:N | b < G.chord (canoe (S:=S) F U i.val)}≤ v)(hp:0 ≤ v): chance S R V (excavation F Y t b)ᶜ ≤ (Y.card:ℝ)*(y+4*v) :=by
   let p(i:Site f):={U:N | i∈ flags t U}
   let A:= ⋃ i∈Y,p i; have hF(i): MeasurableSet (p i):=(flags_open ..).measurableSet; have hA : MeasurableSet A := Finset.measurableSet_biUnion _ (fun i _=>hF i)
   let Q:= univ.filter fun i:F.Free=>i.val.1 ∈Y; let B(i:F.Free):={U:N | b < G.chord (canoe (S:=S) F U i.val)}; let W:=⋃ i∈Q,B i
   have hQ(i):MeasurableSet (B i) := (isOpen_lt continuous_const (G.continuous_chord.comp ((continuous_apply i.val).comp (canoe_cont ..)))).measurableSet
   have hW : MeasurableSet W := Finset.measurableSet_biUnion _ fun i _=>hQ i
   have hs : (excavation (G:=G) F Y t b)ᶜ ⊆ A∪W:=by
      intro i hi; by_cases ht:Healthy t Y i
      · have he: ¬∀ k:F.Free,k.val.1∈Y→ G.chord (canoe (S:=S) F i k.val) ≤ b:= fun he=>hi (show i∈excavation F Y t b from ⟨ht,he⟩) -- infer
        push Not at he; obtain ⟨j,hj,hk⟩:=he; exact Or.inr (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨mem_univ _,hj⟩,hk⟩⟩)
      obtain ⟨j,hj,hb⟩:=Finset.not_disjoint_iff.mp ht; exact Or.inl (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hj,hb⟩⟩)
   have ht' := c_mono V h (landed F t b Y|>.compl) (hA.union hW) hs
   have hQc : Q.card ≤ Y.card*4 := le_trans (Finset.card_le_card_of_injOn (t:=Y×ˢ (Finset.univ:Finset Axis)) (fun i:F.Free=> i.val) (fun i (hi:i∈Q)=>Finset.mem_product.mpr ⟨(mem_filter.mp hi).2,mem_univ _⟩) (Subtype.val_injective.injOn)) (by simp [Axis]) -- coe
   have hg: chance S R V A ≤ Y.card*y:= ((join h _ fun i _=> hF i).trans (Finset.sum_le_sum fun i hi=>hv i hi)).trans_eq (by simp)
   have hh: chance S R V W ≤ Q.card*v := ((join h _ fun i _=> hQ i).trans (Finset.sum_le_sum fun i hi=> hC i (mem_filter.mp hi|>.2))).trans_eq (by simp [Q])
   refine (ht'.trans ((union_bound h hA hW).trans (add_le_add hg hh))).trans ?_; have he:(Q.card:ℝ) ≤ (Y.card:ℝ)*4:=by exact_mod_cast hQc
   linarith only [mul_le_mul_of_nonneg_right he hp]
end YM.MSbar.Heath
