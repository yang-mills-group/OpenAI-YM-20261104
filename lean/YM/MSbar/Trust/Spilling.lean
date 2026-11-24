import YM.MSbar.Trust.Cycling
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{r:Ratio c f}{U W:Config G f}{V:Config G c}{R:Rep G f}{σ C T a v x y δ w D b u t:ℝ}
open Finset
open YM.MSbar.Bulk SectorNext.Vacuum
open Tree
variable (F: Forest S.ratio) (s:F.Slice G)
local notation "N" => Config G f
set_option quotPrecheck false
local notation "σθ"=> Site f
local notation "Wθ"=> F.foldAt
local notation "Q"=> pedal F s
structure Seal (S:StepData c f) (X: Support f)(A:Set (Config G f)):Prop where
    from_here : MeasurableSet A
    within : Sweet S A
    localized : LocalOn (X:Set _) (fun U:Config G f=> U∈ A)
namespace Seal
variable {X Y: Support f}{A B:Set (Config G f)}
lemma combine (h:Seal S X A)(hp:Seal S X B):Seal S X (A∩B):=⟨h.from_here.inter hp.from_here,fun i he U=> and_congr (h.within i he U) (hp.within i he U),fun U V hX=> congr_arg₂ And (h.localized U V hX) (hp.localized U V hX)⟩
lemma neg (h:Seal S X A): Seal S X Aᶜ:=⟨h.from_here.compl,fun i he U=>(h.within i he U).not,fun U V hp=> congr_arg Not (h.localized U V hp)⟩
lemma admits (h:Seal S X A)(ht:X⊆Y):Seal S Y A:= ⟨h.from_here,h.within,fun U V hv=>h.localized U V (agrees_mono hv (coe_subset.mpr ht))⟩
end Seal
variable {X: Support f}{Y : Finset F.Free}{P:Set (Config G f)}
structure Booking (X: Support f) (F: Tree.Forest S.ratio) (τ:F.Slice G): Prop where
    itinerary : ∀ i,τ i≠1 → i.val.1∈X ∧ (((visits i.val.1 (F.hike i.val.1)).toFinset) ⊆ X)
lemma listed (h:Booking X F s) (U V:N) (Y:Support f)(hp:X⊆ Y)(hu:Agrees (Y:Set _) U V): Agrees Y (Q U) (Q V):=by
    intro i hi hh; unfold pedal
    rw [hu _ hi hh]; by_cases he:F.drape s i=1; rw [he]; group
    have hz:i∉ F.trunks:= fun h=>he (F.on_tree _ ⟨_,h⟩); let j:F.Free:=⟨i,hz⟩
    have hq : F.foldAt U i.1= F.foldAt V i.1:= congr_arg Inv.inv (travel_local _ _ U V (agrees_mono hu ?_))
    · rw [hq]
    have hc:= h.itinerary j (fun he'=>he ((F.off_tree s j).trans he'))|>.2.trans hp; intro i hi; exact hc (List.mem_toFinset.mpr hi)
lemma offroad (h:Booking X F s)(V:N)(i:F.Free) (ht:i.val.1 ∉ X): pedal F s V i.val=V i.val :=by
    unfold pedal; rw [F.off_tree, show s i=1 from by_contra (fun hg=> ht (h.itinerary i hg).1)]; group
lemma unspoken (h:Booking X F s)(V:N)(i:Edge (Site f)) (ht:i.1∉ X):pedal F s V i=V i:=by by_cases hc:i∈ F.trunks; unfold pedal; rw [show F.drape s i=1 from F.on_tree _ ⟨i,hc⟩]; group; exact offroad F s h V ⟨i,hc⟩ ht
lemma prior_authority (A:Set N)(h:Seal S X A)(hx:Booking X F s):Seal S X (Q ⁻¹' A):=by
    refine ⟨h.from_here.preimage (pedaling F s|>.measurable),fun t ht U=> ?_,fun U V hv=>h.localized _ _ (listed F s hx _ _ _ subset_rfl hv)⟩
    simp_rw [Set.mem_preimage]; rw [dodge F s _ _ ht]; exact h.within t ht _
lemma traj (A:Set N)(h:Seal S X A) (hx:Booking X F s)(hp:∀ i∈A,flags R.p.threshold (Q i)=flags R.p.threshold i) : Tracks R X Q (spec A) S 1:=by
    have he(i)(hh:spec A i≠0) : i∈ A:=by by_contra h; exact hh (Set.indicator_of_notMem h _)
    refine ⟨fun i hE U=> ?_,fun U V hp _=> ?_, (show Envelope (spec A) from Envelope.piece h.from_here (Envelope.const _) (Envelope.const _)).meas,fun i=>?_,(pedaling F s|>.measurable),fun i hh=> hp i (he i hh), fun U V Y _ hv hg _=> listed F s hx U V Y hv hg,fun i U hi _=>(dodge F s _ _ hi),fun Y U _ hh e he hE=> ?_⟩
    · by_cases hv:U∈A
      · exact (Set.indicator_of_mem ((h.within i hE U).1 hv) _).trans (Set.indicator_of_mem hv (fun _=> (1:ℝ))).symm
      exact (Set.indicator_of_notMem ((h.within i hE U).not.mp hv) _).trans (Set.indicator_of_notMem hv (fun _=> (1:ℝ))).symm
    · unfold spec; simp only [Set.indicator]; split <;> split <;> try rfl
      all_goals grind [h.localized U V hp]
    · unfold spec; by_cases hh:i∈A <;> simp [Set.indicator,hh]
    exact (unspoken F s hx U e (fun i=>disjoint_left.mp hh i he)).symm
variable (hd : S.patch.Branches S.kernel G) (h:Admitted V R S σ C δ T w)
    (hq:Psalm S R v D) (L:MergeProof.Menu.Arsenal R)
include hd h L hq
local notation "H"=> chance S R V
lemma tumble {w':ℝ} {A B Z:Set N} (ha:Seal S X A)(hb:Seal S X B)(hZ:Seal S X Z) (hp:Booking X F s)(hα:Continuous R.eval)(hζ:∀ μ:N,0<R.eval μ)(hD:0 ≤ D)(hv: flags v V=∅)(hw: H Bᶜ ≤ w') (hc: ∀ μ∈ B,boundPress S R V μ ≤ t * boundPress S R V (Q μ)) (ht:0≤t) (hx:0≤x)
    (hy:∀ μ∈B,Q μ ∈ B → flags R.p.threshold (Q μ)=flags R.p.threshold μ)
    (hW: ∀ μ∈A, μ∈B → Q μ∈ B→ Q μ∈Z∧ S.density R.beta μ V * Real.exp (R.exponent μ) ≤ x*S.density R.beta (Q μ) V * Real.exp (R.exponent (Q μ))) : H A ≤ x*H Z + ((1+t)*w' + D*(R.p.mass X 2* Real.exp (X.card*w))) := by
    let B' := Q ⁻¹' B; let q:= A∩B∩B'; let i:=B∩ B'ᶜ; have he' := prior_authority F s B hb hp
    let P:= Bᶜ∪i
    have hr:=journey F s hd h; have hI:Seal S X i:= hb.combine he'.neg
    have hE:Seal S X q:=(ha.combine hb).combine he'
    have hh : H i ≤ t*H Bᶜ := budget_shift h hr hI.from_here hb.from_here.compl hI.within hb.neg.within (Set.subset_univ _) (fun _ hi=>hi.2) (fun p he=> by rw [one_mul]; exact hc p he.1) ht
    have hs : H P ≤ (1+t)*w':= ((union_bound h hb.from_here.compl hI.from_here).trans (add_le_add hw (hh.trans (mul_le_mul_of_nonneg_left hw ht)))).trans_eq (by ring)
    have hm := energy_shift h hr hq L hD hv (traj F s q hE hp (fun i hi=>hy i hi.1.2 hi.2)) hE.from_here hZ.from_here hE.within hZ.within (Set.subset_univ _) (fun i hi=> (hW _ hi.1.1 hi.1.2 hi.2).1) hx hα hζ (fun p he=>by rw [one_mul]; exact (hW _ he.1.1 he.1.2 he.2).2)
    have he:A⊆ q∪ P:=by
       intro i hi; by_cases h:i∈ B
       · by_cases hh:i∈ B'; exact Or.inl ⟨⟨hi,h⟩,hh⟩; exact Or.inr (Or.inr ⟨h,hh⟩)
       exact Or.inr (Or.inl h)
    have hP:= hb.from_here.compl.union hI.from_here
    exact (((c_mono V h ha.from_here (hE.from_here.union hP) he).trans (union_bound h hE.from_here hP)).trans (add_le_add hm hs)).trans_eq (by ring)
end YM.MSbar.Heath
