import YM.LocalLTE.Ballot.Swell
import YM.LocalLTE.Marked.Destiny
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Toll


/-! # Regular script for second unforced log. Keeps repeats. No Hessian subtraction yet!

Anchor on UNION site; pays factor exp surplus at endpoint, doesn't move
 each genealogy to fresh center. Keep honest clustered labels.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.March
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained Gas Ursell
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {I : Finset (Tubular f G)} {η r q a Y W d C' A b s μ C v B: ℝ} {Ñ : ChartRatio G}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R} {Ξ : Utopia H j v d r C' χ}
open Next.Foundations

open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt

namespace Captain
variable (N : Captain H j C' d v Y A b r B q k χ)
variable (p : Clusters H.ThinP)
open Greenbelt


open Merge Merge.Palette Height Daisy Lotus
-- every factor still selected independently.R.indices attached later. purposes geometry active.Down.
variable {ι:Type}[Fintype ι] (M:ι→Lotus.Leaf R)(rA:ι→ℝ)(he:∀ i, 0≤rA i)
set_option quotPrecheck false
local notation "χz"=> Merge.Palette.sign M S
local notation "τ"=> Merge.Tickets (Merge.Palette.sign M S)
variable (V:Config G c) (R': Merge.Tickets (Merge.Palette.sign M S))(i:H.ThinP)
open LocalLTE.Fan
omit [Fintype ι] in
lemma oneScene (Q':Team R) (Y:Lotus.Leaf R)(hp:Q'.own={Y}) {F:Forest S.ratio}(X:Coat T F)(k:Molecule S) (Ñ:ChartRatio G)(a:ℝ)(l:ℕ) (μ:ℝ):Q'.qlocal4a_picture X k a μ Ñ l= Y.picture X k a μ Ñ l:=by
    have h (X:Coat T F): Q'.qlocal4a_grove X k a μ Ñ l=Y.grove X k a μ Ñ l:=by
       unfold Team.qlocal4a_grove Leaf.grove; split; swap; · rfl
       apply congr_arg likely; funext j; unfold Team.qlocal4a_cinema Leaf.cinema
       simp_rw [Team.qlocal4a_floret, Team.signs, hp, Finset.image_singleton, Finset.singleton_subset_iff,Team.paidU,hp, Finset.prod_singleton, Finset.sdiff_singleton_eq_erase]
    unfold Team.qlocal4a_picture Leaf.picture; simp_rw [h]
-- maybe omit warning
lemma nilScene (Q':Team R) (hp:Q'.own=∅) {F:Forest S.ratio}(X:Coat T F)(k:Molecule S) (Ñ:ChartRatio G)(a:ℝ)(l:ℕ) (μ:ℝ):Q'.qlocal4a_picture X k a μ Ñ l=fringe X a μ k R Ñ l:=by
    have h (X:Coat T F): Q'.qlocal4a_grove X k a μ Ñ l=shelter X a μ k R Ñ l:=by
       unfold shelter Team.qlocal4a_grove; split; swap; · rfl
       unfold seating; dsimp only; apply congr_arg likely; funext j; unfold Team.qlocal4a_cinema bars
       simp_rw [Team.qlocal4a_floret, Team.signs, hp, Finset.image_empty, Finset.empty_subset,if_true, Team.paidU,hp, Finset.prod_empty, Finset.sdiff_empty,one_mul]
    unfold Team.qlocal4a_picture Stained.fringe; simp_rw [h]
open Daisy.Charity
omit [Fintype ι] in
lemma mona (a:ι): Captain.waltz H χ M i (Merge.Tickets.mono _ a) V= Charity.libs (M a) H χ V i:= congr_arg likely (funext (fun j=>oneScene _ _ (by simp [Palette.team, Tickets.mono]) _ _ _ _ _ _)) -- order
omit [Fintype ι] in
lemma noneP : Captain.waltz H χ M i (Merge.Tickets.none _) V= leaflet H χ V i:= congr_arg likely (funext (fun j=> nilScene _ (by simp [Palette.team, Tickets.none]) _ _ _ _ _ _))
variable (a:ι)(p: Clusters H.ThinP)
-- Piece from old representation. Specialized injection reading same Star.S.T. Deterministic.
noncomputable def gateP (j:Option (Fin p.fst)): Oscars M p := fun i=> if i=j then Merge.Tickets.mono _ a else Merge.Tickets.none _
local notation "Tι"=> gateP M a p -- arg order p M a
omit [Fintype ι]
lemma tag_yes (j:Option (Fin p.fst)): YM.LocalLTE.Fan.Enter M H ⟨p, Captain.gateP M a p j⟩:= ⟨j, a,by change a∈(Captain.gateP M a p j j).val; unfold gateP; rw [if_pos rfl];exact Finset.mem_singleton_self _⟩
lemma singularPin : Function.Injective (Captain.gateP M a p):=by
     intro i j h; by_contra e; apply singleton_ne_empty a; have h':= congr_fun h i; unfold gateP at h'; rw [if_pos rfl,if_neg e] at h'; exact congr_arg Subtype.val h'
lemma stampP (j:Option (Fin p.fst)): pearl p M rA (Captain.gateP M a p j)=rA a:=by
    unfold pearl gateP; rw [Finset.prod_eq_single j]; simp [Tickets.mono]; rintro i hi ht; rw [if_neg ht]; simp [Tickets.none]; simp
lemma speaksP : Charity.matin (M a) H p χ = ∑ j:Option (Fin p.fst),YM.LocalLTE.Fan.exactE M H χ ⟨p,Captain.gateP M a p j⟩:=by
   funext V; rw [Finset.sum_apply]; unfold matin; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
   unfold exactE; simp only [if_pos (Captain.tag_yes M a p i)]; unfold Captain.wingTerm; dsimp only
   rw [← Finset.prod_erase_mul (Finset.univ (α:=Option (Fin p.fst))) _ (Finset.mem_univ i)] -- target occurrence? picks univ.erase i too? lemma expects univ. 
   have hz j (hp:j≠i): waltz H χ M (p.snd j) (Captain.gateP M a p i j) V = leaflet H χ V (p.snd j):= by unfold gateP; rw [if_neg hp];exact Captain.noneP M V _
   let g j:= leaflet H χ V (p.snd j)
   have hp : waltz H χ M (p.snd i) (Captain.gateP M a p i i) V= Charity.libs (M a) H χ V (p.snd i):=by unfold gateP; rw [if_pos rfl]; exact Captain.mona ..
   rw [hp,prod_congr (g:=g) rfl fun j hj=> hz j (Finset.mem_erase.mp hj).1] -- maybe LHS? test
   unfold g; ring
end Captain
end YM.ConnectedActivityE6.Blaze.March
