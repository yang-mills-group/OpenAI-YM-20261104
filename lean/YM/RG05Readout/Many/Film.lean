import YM.RG05Readout.Many.Consider
/-!
# Full/restricted ancestor polynomial identity

When reopening at m we still evaluate all costs from the authentic physical
line. Reopen via openings with a Cartesian vanishing factor at m, and prove
it coincides with the costs specialization (no absolute joint estimates
claimed outside paid radii or on other slot decompositions). Counterterm
lineages unchanged. `Replay.actual` will retain precisely this actual density.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
section alg
variable {V W I Z:Type} [Fintype V][DecidableEq V][Fintype W][DecidableEq W] {B C:Census V} {R S:Census W}
variable {G:Gauge}{n:Side}
-- narrow preserves `move` even when image is zero at target. Is natur transformation on licensed square window.
variable {a: V→W} (l:V→ℂ)
omit [Fintype V] in
lemma through {x:B.Mode} (h:B.choices⊆C.choices)(c:ℂ) : narrow h (Poly.send (route h x) c)= Poly.send x c:=by
    ext i; rw [narrow_right,Poly.part_send, Poly.part_send]; by_cases ht:i=x; subst i; rw [if_pos rfl,if_pos rfl]
    rw [if_neg ht,if_neg ?_]; exact fun he=>ht (Subtype.ext (show i.val=x.val from congr_arg (fun q:C.Mode=>q.val) he))
omit [Fintype V] in
lemma through0 (x:C.Mode)(h:B.choices⊆C.choices)(hx:x.val∉B.choices)(c:ℂ): narrow h (Poly.send x c)=0 :=by
    ext i; rw [narrow_right,Poly.part_send]; apply if_neg; intro hi; apply hx; rw [← hi]; exact i.property
-- setup diamond. This uses permit direction.
omit [Fintype V] [Fintype W] in
lemma square (h:B.choices ⊆ C.choices)(ht:R.choices⊆S.choices)(hg:License R B a)(hv:License S C a) (u:Poly C):
     narrow ht (feed l hv u) = feed l hg (narrow h u):=by
    rw [← Poly.studs u];simp_rw [map_sum]; refine Finset.sum_congr rfl fun i _=>?_
    by_cases he:i.val∈ B.choices
    · let j:B.Mode:=⟨_,he⟩; let v:=u.part i; let y:= (∏ l'∈i.val,l l')*v
      rw [show i=route h j from rfl,through h,mouth l,mouth l]; change narrow ht (move C S a (route h j) y)=move B R a j y
      unfold move; by_cases hu: Lit R a j.val
      · have hx: Lit S a (route h j).val:=⟨ht hu.1,hu.2⟩; rw [dif_pos hu,dif_pos hx,show hx.climb=route ht hu.climb from rfl,through]
      rw [dif_neg hu]; split
      next hp=> exact through0 _ ht (fun hz=> hu ⟨hz,hp.2⟩) _
      next hp=> rw [map_zero]
    rw [through0 i h he,map_zero,mouth l]; unfold move; split
    next hg'=> exact through0 _ ht (fun hx=> he (hg i.val ⟨hx,hg'.2⟩)) _
    next=> rw [map_zero]
lemma birth_choice (P:Rep G n) (F:V→ Config G n→ℂ)(h:B.choices ⊆ C.choices)(U:Config G n) : narrow h (birth C P F U)= birth B P F U:=by
    unfold birth narrow; rw [map_smul, YM.Multi.pass_map _ _ (mute C _ ) ((feed_quiet ..).trans (mute ..)), feed_mach]; simp
-- integrable naturality. Keep arbitrary F dim fixed. apply on any finset branch.
omit [Fintype V][Fintype W] in
lemma amp_live {c:Side}(M:Poly B→ₗ[ℂ]Poly R) (Q:StepData c n){x:ℝ}{F:Config G n→ Poly B}(h:Integrable F (prior G _))(ht:Q.IsKernel x G):
      Q.push x (fun i=>M (F i)) = fun U=> M (Q.push x F U):=by
   let L:= M.toContinuousLinearMap.restrictScalars ℝ; funext U; have hx:= L.integral_comp_comm (StepData.push_slice ht U F h)
   unfold StepData.push; change ∫ i,Q.density x i U • L (F i) ∂prior G _= L (∫ i,Q.density x i U • F i ∂prior G _); simp_rw [← L.map_smul]; exact hx
end alg
variable {G:Gauge} {C:Family G} {n m p N d:ℕ}{V: ℕ→Type}[∀ i,DecidableEq (V i)][∀ i,Fintype (V i)] {W:Type*}
    {D:Address.Rail C} {w:Worth}{r:ℕ→ℕ} {j b k g:ℕ}
set_option quotPrecheck false
local notation "Z₀"=> C.path.levels
local notation "t₁"=> C.path.levels.budget
local notation "K"=> C.path.levels.clock
local notation "P!"=> C.side
local notation "Y"=> C.path.rep N p
local notation "L!"=> C.path.levels.clock.op
variable (A:Planner C p n V W) {H G':∀ i:ℕ,Census (V i)} (s:W→ℕ)
local notation "Λ"=>A.labelY
local notation "Φ"=>A.narrows
local notation "r₀"=>A.supportX
variable {F:∀ i:ℕ, Config G (C.side i p)→Poly (H i)}{U:∀ i:ℕ, Config G (C.side i p)→Poly (G' i)}

omit [(i:ℕ)→Fintype (V i)] in
lemma reels_write (hp:n≤b)(hg:b≤ m) (hc:∀ i:ℕ,∀ hi:b ≤ i,i< m→ License (H i) (H (i+1)) (Prod.fst ∘ (Φ i (hp.trans hi)))) (X' : Config G (C.side m p) → Poly (H m))(N : ℕ):
    ∃ F:∀ i:ℕ, Config G (C.side i p)→Poly (H i), Replay A s (H:=H) hp m F N ∧ F m=X':=by
      induction hg using Nat.decreasingInduction with
      | self=> refine ⟨Function.update (fun _=>0) m X',⟨fun _ hi h=>by omega⟩,Function.update_self ..⟩
      | of_succ i h ih=>
         have hR:= hp.trans i.le_succ
         obtain ⟨F,hF,hf⟩:= ih hR (fun x hx=>hc x (i.le_succ.trans hx))
         let x:=downdraft (N:=N) A H s i hp (hc i le_rfl h) (F (i+1)); let G':=Function.update F i x
         refine ⟨G',⟨fun j hi hv=>?_⟩,Eq.trans (Function.update_of_ne h.ne' ..) hf⟩
         intro P'; rcases eq_or_lt_of_le hi with ht|ht
         · subst j; unfold G'; rw [Function.update_self,Function.update_of_ne (by omega : i+1 ≠ i)]; exact ⟨_,rfl⟩ -- maybe hole
         obtain ⟨V,hV⟩:= hF.downhill (V:=V) _ ht hv; unfold G'; rw [Function.update_of_ne ht.ne',Function.update_of_ne (show j+1≠i by omega)]; exact ⟨V,hV⟩


omit [(i:ℕ)→Fintype (V i)] in
lemma Replay.live (hp:n ≤ b)(hf:Replay (H:=H) A s hp m F N)(h:Integrable (F m) (prior G _)) (_ht:m≤N){i:ℕ} (he:b≤ i)(hi:i≤ m) : Integrable (F i) (prior G _):=by
   induction hi using Nat.decreasingInduction with
   | self=>exact h
   | of_succ i hi ih=>
       obtain ⟨g,hg⟩:=hf.downhill (V:=V) _ he hi; rw [hg]; exact feed_live g _ (StepData.push_integrable ((Z₀).transition_mass ..) _ (ih (he.trans i.le_succ)))
-- ht used??? kernel transition all ℝ so linter
omit [(i:ℕ)→Fintype (V i)] in
lemma Replay.narrowing (hp:n≤b)(hq:n≤j)(he:j≤b)(hf:Replay (H:=H) A s hp m F N)(hh:Replay (H:=G') A s hq m U N)
    (hg:∀ i, b ≤ i→ (H i).choices ⊆ (G' i).choices) (hv:b ≤ m)(hX:Integrable (U m) (prior G _)) (_ht:m≤N)
    (hu:∀ X,F m X=narrow (hg m hv) (U m X)) {i:ℕ} (hi:b ≤ i)(hz:i ≤ m) (U':Config G (C.side i p)) : F i U'=narrow (hg i hi) (U i U'):=by
   induction hz using Nat.decreasingInduction with
   | self=> exact hu U'
   | of_succ i hz ih=>
       obtain ⟨g,hL⟩:=hf.downhill (V:=V) i hi hz; obtain ⟨l,hR⟩:=hh.downhill (V:=V) i (he.trans hi) hz; rw [hL,hR]; unfold downdraft
       rw [show F (i+1) = _ from funext (ih (hi.trans i.le_succ))]; dsimp only
       let L:=narrow (hg (i+1) (hi.trans i.le_succ)); let a':= U (i+1); have hx:= hh.live A s hq hX _ht (he.trans (hi.trans i.le_succ)) hz
       have hi' : (L! i p).push ((Y (i+1)).beta) (fun z=> narrow (hg (i+1) (hi.trans i.le_succ)) (U (i+1) z)) U'= L ((L! i p).push ((Y (i+1)).beta) a' U') := congr_fun (amp_live L.toLinearMap _ hx ((Z₀).transition_mass i p ((Y (i+1)).beta))) _
       rw [hi']; exact (square _ (hg (i+1) (hi.trans i.le_succ)) _ g l _).symm
end YM.RG05Readout.Many
