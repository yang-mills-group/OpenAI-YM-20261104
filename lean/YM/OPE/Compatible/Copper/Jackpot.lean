import YM.OPE.Compatible.Copper.Tarnish
/-!
# Lens derivative and truncation for signed root balance.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Pixel
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset Extraction Word Spec
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells CutOrder Arcade
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X I : Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){U F:Finset X}
   {G:Gauge}{C:Family G}{Λ:Extraction.Order}{S:Table C.book}(T:Spec.Final C Λ S)(A:Allot C) (P:Prescription T.sector.derivatives)
variable (p:X→ C.book.Token) (u:X)(hp:Crown U)(hu:u∈rest U){t:ℕ}(e:Exterior C.book) -- del
set_option quotPrecheck false
local notation "L"=> T.sector.derivatives
local notation "V"=> brim D U
local notation "W"=> brim D (Arboreal.trim U u)
local notation "J"=> glen D U u
local notation "p₀"=> picked V p
variable (hΓ:Org.Grill C Λ)
-- grid statements. membership at root allUp. send to certified aperture here. use finite sheet
include hΓ hp hu T
lemma storyBook : ∀ᶠ i in atTop,∃ b A:ℝ,0 < b∧ 0 ≤ A∧ ∀ W':ℕ,i ≤ W' → ∀ {k n d d':ℕ} (y:X→ Cover)(p':X→ C.book.Token), Screen (picked V (C.S.gridPoint W' ∘ y))→ Screen (picked W (C.S.gridPoint W' ∘ y)) → (∀ i∈allUp D U,‖C.S.gridPoint W' (y i)‖<b)→ (∀ i∈ brim D U,S.classTokens (p' i)= S.classTokens (p i))→ ∀ {x x' z z':ℝ}{a:C.label d}{s:C.label d'}, TokenMine D C Λ U (picked V p') u y W' i k n d d' a s x x' z z'→ ‖(Prescription.reading S (picked V (C.S.gridPoint W' ∘ y)) p₀ 0 e-Prescription.reading S (picked W (C.S.gridPoint W' ∘ y)) (picked W (update p u (⟨d,a⟩:C.book.Token))) 0 e)- S.spectra d' (S.project d' s) e‖≤ z'*A:=by
   obtain ⟨b,hb,hc⟩:= cleared e; filter_upwards [viewed_root (T:=T) hΓ e.letter hb] with i ⟨B,hB,he⟩; refine ⟨b,B,hb,hB,fun W' hw k n d d' y p' hS hS' hx hz x x' z z' a s hh =>?_⟩
   let U':=C.S.gridPoint W' ∘ y; have hI (v: Finset X)(hv:v ⊆ allUp D U)(he:Screen (picked v U')):Injective (beside (picked v U') (bearing e)):= beside_distinct.mpr ⟨he.coin,(beside_distinct.mp (bearing_clear e)).2.1, fun i j h'=>by
        have hx:=hx i.val (hv i.2); change ‖picked v U' i‖ < b at hx; rw [h'] at hx; have hu:=hc.openSpace j; rw [zero_sub,norm_neg] at hu; linarith⟩
   have hV := hI _ (by exact subset_union_right) hS; have hV':= hI _ (brim_under D U _ (filter_subset ..)) hS'
   change Injective (beside (picked (brim D (Arboreal.trim U u)) U') (bearing e)) at hV'
   rw [← Prescription.one_test _ _ _ T.room.kernel]
   unfold U' at hV hV'; unfold Prescription.reading; simp only [sub_zero,if_pos (bearing_clear _), if_pos hV, if_pos hV']; exact he W' hw D U u hp hu p p' hz y hS hS' hh _ hc hV hV' none
lemma storyFunds (e:Finset (Mode L)) : ∀ᶠ i in atTop,∃ b A:ℝ,0 < b∧ 0 ≤ A∧ ∀ W':ℕ,i ≤ W' → ∀ {k n d d':ℕ} (y:X→ Cover)(p':X→ C.book.Token), Screen (picked V (C.S.gridPoint W' ∘ y))→ Screen (picked W (C.S.gridPoint W' ∘ y)) → (∀ i∈allUp D U,‖C.S.gridPoint W' (y i)‖<b)→ (∀ i∈ brim D U,S.classTokens (p' i)= S.classTokens (p i))→ ∀ {x x' z z':ℝ}{a:C.label d}{s:C.label d'}, TokenMine D C Λ U (picked V p') u y W' i k n d d' a s x x' z z'→ ∀ t∈e, ‖(P.ope t (picked V (C.S.gridPoint W' ∘ y)) p₀ 0-P.ope t (picked W (C.S.gridPoint W' ∘ y)) (picked W (update p u (⟨d,a⟩:C.book.Token))) 0)- P.test t d' (S.project d' s)‖≤ z'*A:=by
   let J':= e.biUnion (fun i=> (P.sheet i).support); filter_upwards [eventually_all.mpr (fun i:J'=> storyBook D T p u hp hu i.val hΓ)] with i hi; choose b A hb hA hJ using hi
   obtain ⟨m,hm,hB⟩:= ((show ∀ᶠ v:ℝ in 𝓝[>] 0,0<v from self_mem_nhdsWithin).and ((eventually_all.mpr fun i:J'=>ge_mem_nhds (hb i)).filter_mono nhdsWithin_le_nhds)).exists
   let g (x:Exterior C.book):=if h:x∈J' then A ⟨x,h⟩ else 0; let f (i:Mode L):=∑ j∈(P.sheet i).support,‖P.sheet i j‖*g j
   have hf x: 0 ≤ g x:=by unfold g; split <;> first|exact hA _|exact le_rfl
   have hF i:0 ≤ f i:=Finset.sum_nonneg fun x _=> mul_nonneg (norm_nonneg _) (hf _)
   refine ⟨m,∑ i∈e,f i,hm,Finset.sum_nonneg (fun i _=> hF i),fun K hK k n d d' y p' H H' hh hx x x' z z' a s hΛ t ht=>?_⟩ -- conflict H
   have hY(j:Exterior C.book)(hP:j∈(P.sheet t).support): ∃ hj:j∈J', g j=A ⟨j,hj⟩:=by
       have hn:j∈J':=mem_biUnion.mpr ⟨_,ht,hP⟩; exact ⟨hn,dif_pos hn⟩
   have hV:0≤ z':=(token_fees D u hΛ).2; let r(j:Exterior C.book):= S.spectra d' (S.project d' s) j; let Q:=C.S.gridPoint K ∘ y
   unfold Prescription.test Prescription.ope; rw [computes, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib] -- locate computes
   simp_rw [← mul_sub]
   refine (norm_sum_le ..).trans (le_trans ?_ (mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun b _=> hF b) ht) hV)); unfold f; rw [Finset.mul_sum]; refine Finset.sum_le_sum (fun j hp'=>?_); obtain ⟨hj,hg⟩:= hY j hp'
   rw [norm_mul,hg]; exact (mul_le_mul_of_nonneg_left (hJ ⟨j,hj⟩ K hK y p' H H' (fun i hi=> lt_of_lt_of_le (hh _ hi) (hB _)) hx hΛ) (norm_nonneg _)).trans_eq (by ring)
end YM.OPE.Arboreal.Pixel
