import YM.RG05Readout.Shadows.Issued
import YM.RG05Readout.Capture.Succ
/-!
# Gale of the complete polynomial along an actual branch

Commission cases from genuine field launch: before costs, equate root modes
through the shot to the *unnormalized* Wilson law. No estimate on the
reciprocal spent yet. Proof for arbitrary products including finite replicated
trials. K retained by Energy producers, not an input to this lemma.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Records
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{V: ℕ→Type}[∀ i,DecidableEq (V i)][∀ i,Fintype (V i)] {W:Type*}
    {j b k g:ℕ}
set_option quotPrecheck false
local notation "X!"=>C.side N p
local notation "λ₁"=> C.path.levels.clock.op
local notation "R₀"=> C.path.rep N p N
local notation "gustC" => gust C.path N p N

section combineV
variable {J I Z:Type}[DecidableEq I][Fintype I][DecidableEq J][Fintype J]
    {R:Census I}{S:Census J}
lemma blend_birth {n:Side}(P:Rep G n)(F:I→ Config G n→ℂ){a:I→J}(l:I→ℂ)(hc:License S R a): birth S P (Many.combine a l F)= fun U => feed l hc (birth R P F U):=by
    funext U; unfold birth; rw [map_smul,YM.Multi.pass_map _ _ (mute R _) ((feed_quiet ..).trans (mute ..)),feed_mach]; congr 4
    funext j; unfold Many.combine; rw [Finset.sum_apply]; apply sum_congr rfl; intro i _; split; rfl; change (0:ℂ)*_= _; rw [zero_mul]
omit [Fintype I] [Fintype J] in
lemma gale (L: Poly R→ₗ[ℂ]Poly S)(h:m ≤ N)(F: Config G (C.side N p)→ Poly R)(ht: Integrable F (prior G _)) :
    gust C.path N p N (fun U=> L (F U)) m h= fun U=> L (gust C.path N p N F m h U):=by
    induction h using Nat.decreasingInduction with
    | self=> rw [gust_base]; simp_rw [gust_base]
    | of_succ i hi ih=> rw [gust_step _ _ _ _ _ hi, ih]; simp_rw [gust_step _ _ _ _ _ hi]; exact amp_live _ _ (gust_live _ _ _ _ _ ht hi) (C.path.levels.transition_mass ..)

lemma blended (F: I→ Config G (C.side N p)→ℂ){a:I→J}(l:I→ℂ)(hc:License S R a)(h:m ≤ N)(hp:Integrable (birth R (R₀) F) (prior G _)) :
    Integrable (birth S (R₀) (Many.combine a l F)) (prior G _) ∧
    gust C.path N p N (birth S (R₀) (Many.combine a l F)) m h= fun U=>feed l hc (gust C.path N p N (birth R (R₀) F) m h U):=by
    rw [blend_birth _ _ l hc]; exact ⟨feed_live hc l hp,gale (feed l hc).toLinearMap h _ hp⟩
section polish
open Ribbons
variable (T:Fibers I J) (U:Unit×I→ℂ) {H:Census (Unit×I)}{B:Census (Unit × J)} (hp : Pantry.Policy T H B)
local notation "U!"=> ManyCopies.partialGroup Unit T
variable {n:Side}
lemma spice_entry (P:Rep G n)(L:I→ Config G n→ℂ)(u:I→ℂ): spice R u (birth R P L)= birth R P (fun i X=> u i+L i X):=by
   unfold spice birth; funext X; let K:=∑ i: I,Poly.send (R.fire i) (u i); let f i:=L i X
   rw [mul_smul_comm,← pass_add (mute R u) (mute R f)]; unfold Mach;rw [←Finset.sum_add_distrib]; congr 2
   apply sum_congr rfl; intro i _; ext t; rw [Poly.part_plus]; simp_rw [Poly.part_send]; split; rfl; rw [add_zero]
lemma pilot_entry (P:Rep G n)(L:Unit ×I→ Config G n→ℂ)(X:Config G n): Pantry.pilot T hp (birth H P L X)= birth B P (fun j Y=> ∏ i ∈ (U!).contents j,L i Y) X:=by
    ext i; let t:H.Mode:=⟨_,hp i⟩; change (birth H P L X).part t= _; unfold birth Mach; rw [Poly.part_smul,Poly.part_smul,pass_fire,pass_fire]; exact congr_arg _ (Fibers.prod_plena ..)
set_option maxHeartbeats 450000 in
lemma brewed (L:Unit × I→ Config G (C.side N p)→ℂ)(h:m ≤ N)(ht:Integrable (birth H (R₀) L) (prior G _)) :
    let Θ:= fun j:Unit × J=> fun X=> ∏ i∈ (U!).contents j,(U i+ L i X)
    Integrable (birth B (R₀) Θ) (prior G _) ∧
    gust C.path N p N (birth B (R₀) Θ) m h= fun V=> Pantry.pilot T hp (spice H U (gust C.path N p N (birth H (R₀) L) m h) V):=by
    intro Θ; let K: Poly H→ₗ[ℂ] Poly H:=LinearMap.mulLeft ℂ (Poly.pass (Mach H U)); let K':=(Pantry.pilot T hp).comp K; let F:= birth H (R₀) L
    have hv: birth B (R₀) Θ= fun X=> K' (F X) :=by
        rw [show birth B (R₀) Θ=fun X' =>Pantry.pilot T hp (birth H (R₀) (fun i X'=> U i+L i X') X') from funext (fun X'=> Eq.symm (pilot_entry T hp (R₀) (fun i X'=> U i+L i X') X')), ←spice_entry]; rfl
    rw [hv]; exact ⟨(K'.toContinuousLinearMap.restrictScalars ℝ).integrable_comp ht,gale K' h F ht⟩
end polish
end combineV
section path
variable (A:Planner C p n V W) (s:W→ℕ) {H:∀ i:ℕ,Census (V i)} (hm:m≤ N)
local notation "Ω" => A.narrows
local notation "φ"=> A.labelY
variable {F:∀ i:ℕ, Config G (C.side i p)→Poly (H i)}
abbrev windstep (hi:n ≤ i)(L:V (i+1)→ Config G (C.side N p)→ℂ): V i→ Config G (C.side N p)→ℂ:=
     let g := Prod.fst ∘ Ω i hi
     Many.combine g (fun x=> budwgt C p i (s (φ i (g x)))) L
variable (T:∀ i:ℕ,V i→ Config G (C.side N p)→ℂ)(ht: n ≤ b)
include hm
lemma reimburses (hp:Replay A s (H:=H) ht m F N) (hU: ∀ k:ℕ,∀ h:b ≤ k,k < m → T k= windstep A s (ht.trans h) (T (k+1)))
   (hx:F m=gust C.path N p N (birth (H m) (R₀) (T m)) m hm)(hy:Integrable (birth (H m) (R₀) (T m)) (prior G _))
   (hl:b ≤ i)(hi:i ≤ m) : Integrable (birth (H i) (R₀) (T i)) (prior G _) ∧ F i=gust C.path N p N (birth (H i) (R₀) (T i)) i (hi.trans hm):=by
    induction hi using Nat.decreasingInduction with
    | self=> exact ⟨hy,hx⟩
    | of_succ i hi ih=>
       obtain ⟨hv,Hv⟩:=hp.downhill (V:=V) _ hl hi; obtain ⟨hΘ,hΘ'⟩:= ih (hl.trans i.le_succ)
       let l:=Ω i (ht.trans hl); let a:=T (i+1); let v':= birth (H (i+1)) (R₀) a; let X' : V (i+1)→ℂ:= fun j=>budwgt C p i (s (φ i (l j).fst)); let hi':= hi.trans_le hm
       rw [hU i hl hi]; have he:= blended a X' hv hi'.le hΘ
       refine ⟨he.1,?_⟩; rw [Hv,hΘ']; refine Eq.trans ?_ he.2.symm; change _= fun U=> feed X' hv (gust C.path N p N v' i _ U); simp_rw [gust_step C.path N p N v' hi']; rfl
end path
end YM.RG05Readout.Records
