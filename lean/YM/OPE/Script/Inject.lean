import YM.OPE.Script.Issue
/-!
# Inject the one alternative using the SAME Safe cells.

Can also replace a dirty/lens-bearing singleton, as long as (now) the other
marks in that cell are clean. That allows matching again at the root after
using a match inside one nested branch. Keep disjointness through every
level; no product-kernel factorization within a cell, only linearity there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Patrol
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory Set
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open GridApprox Cells Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {G:Gauge}{n:Side}{I J : Type} [Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    {A:History G}
set_option quotPrecheck false
local notation "K" => Finset
variable {N p i j k : ℕ} {s: i≤N}
local notation "V" => Site (A.S.side j p)
local notation "R" => A.rep N p
local notation "f" => A.S.side N p
local notation "c" => A.S.side i p
local notation "T" => tilesAt A.S p
local notation "β" => A.β N p N
namespace Script
variable {z: I→Site (A.S.side j p)}{F:I→ Config G (A.S.side N p)→ℂ} {hk:j ≤ i} {hz:i ≤ N} {Q:Config G (A.S.side i p)→ Poly (Bud I)} {d : K I}
def jet (Q:Config G n→Poly (Bud I)) (j:I) (u:Config G n→ℂ) (U:Config G n):= Q U * (1+Poly.send ((Bud I).fire j) (u U))
variable (b:I) {U: Config G (A.S.side i p)→ℂ} (hp:Script A N p hk hz z d Q F)
lemma clear_dis {a : Finset I}{P:K V} (he:Disjoint P ((a∩insert b d).image z)): Disjoint P ((a∩d).image z) := Disjoint.mono_right (Finset.image_mono z (Finset.inter_subset_inter_left (Finset.subset_insert b d))) he
lemma part_int {μ:Measure (Config G n)}{Q:Config G n→Poly (Bud I)}(hp: Integrable Q μ) (a): Integrable (fun i=>(Q i).part a) μ:= ((Poly.get a).restrictScalars ℝ).integrable_comp hp
lemma lower_jet {u:Config G n→ℂ} {Q:Config G n→Poly (Bud I)} (U:Config G n)(a:K I): (jet Q b u U).part (Fibers.mark a)= (Q U).part (Fibers.mark a) + (if b∈a then (Q U).part (Fibers.mark (a\{b})) * u U else 0):=by unfold jet; rw [mul_add,mul_one, Poly.part_plus]; rw [show (Bud I).fire b=Fibers.mark {b} from rfl, Fibers.part_send_mul a {b}]; simp
lemma int_jet {u:Config G n→ℂ} {Q:Config G n→Poly (Bud I)} (hu: Envelope u)(h:Integrable Q (prior G _)) : Integrable (jet Q b u) (prior G _):=by
   apply integrable_pi_iff.mpr; intro i; change Integrable (fun U=>(jet Q b u U).part (Fibers.mark i.val)) _; simp_rw [lower_jet b]; split; next hb=> exact (part_int h i).add (((part_int h _)).mul_bdd hu.meas.aestronglyMeasurable (Eventually.of_forall hu.cost.choose_spec))
   next=> simp_rw [add_zero]; exact part_int h _
include hp
lemma fired (hh:Safe A N p hk (z b) U)(hF:∀ i∈d,z i=z b→i=b) : Script A N p hk hz z (insert b d) (jet Q b U) (Function.update F b (F b+backTo A N p hz U)):=by
   let G':= Function.update F b (F b+backTo A N p hz U); have he:= hh.calls hz
   refine ⟨int_jet b he hp.budget,fun i=>?_,?_⟩
   · by_cases hj:i=b; subst i; rw [Function.update_self]; exact (hp.cost b).addC (backTo_env _ _ _ _ he)
     rw [Function.update_of_ne hj]; exact hp.cost _
   intro a P ht W hw; let S:=a\{b}; let f' x:=fineJob W P x; let q' x:=fineJob (fun v=> backTo A N p hz (W v)) P x
   have hs:= hp.exists_budget a P (clear_dis b ht) W hw
   have hZ (p : Finset I)(hc:b ∉ p)(U:Config G f): fineJob G' p U=fineJob F p U:= prod_congr rfl fun i hi=> congr_fun (Function.update_of_ne (ne_of_mem_of_not_mem hi hc) ..) _
   simp_rw [lower_jet b]; split; swap
   next hv=> simp only [add_zero]; simp_rw [show ∀ u,fineJob (Function.update F b _) a u =_ from fun u=> hZ a hv u]; exact hs
   next hv =>
   have hb:z b ∉ P:=fun h=> Finset.disjoint_left.mp ht h (mem_image_of_mem _ (Finset.mem_inter.mpr ⟨hv,mem_insert_self ..⟩))
   let Y:=Function.update W (z b) U; have hP : ∀ i∈insert (z b) P, Safe A N p hk i (Y i) := by intro i hi; rcases mem_insert.mp hi with hi|hi; subst i; unfold Y; rw [Function.update_self]; exact hh; unfold Y; rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hb)]; exact hw i hi
   have hξ := hp.exists_budget S (insert (z b) P) (by
      apply Finset.disjoint_left.mpr; intro v h hj; obtain ⟨i,hi,rfl⟩:=mem_image.mp hj; obtain ⟨hK,hK'⟩:=Finset.mem_inter.mp hi; rcases mem_insert.mp h with h|h
      · exact (Finset.notMem_singleton.mp (Finset.mem_sdiff.mp hK).2) (hF i hK' h)
      exact Finset.disjoint_left.mp ht h (mem_image_of_mem _ (Finset.mem_inter.mpr ⟨Finset.sdiff_subset hK,mem_insert_of_mem hK'⟩))) Y hP
   have hW(v): (∏ i ∈ insert (z b) P,Y i v)=U v*f' v:=by rw [prod_insert hb,show Y (z b)=_ from Function.update_self ..]; exact congr_arg _ (prod_congr rfl (fun i hi=> congr_fun (Function.update_of_ne (ne_of_mem_of_not_mem hi hb) ..) _))
   have hx(v): (∏ i ∈ insert (z b) P,backTo A N p hz (Y i) v)= backTo A N p hz U v * q' v:= by rw [prod_insert hb, show Y (z b)=_ from Function.update_self ..]; apply congr_arg (_ * ·); exact prod_congr rfl fun i hi=> congr_arg (fun f'=> backTo A N p hz f' v) (Function.update_of_ne (ne_of_mem_of_not_mem hi hb) ..)
   let l := Fibers.mark a; let X := Fibers.mark S; let b' (W:Config G f):ℂ:= bare β W; let V' W:=b' W*fineJob F a W*q' W; let W' W:= b' W*fineJob F S W*(backTo A N p hz U W*q' W); let L W:= (Q W).part l*f' W; let K' W:=(Q W).part X*(U W*f' W)
   simp_rw [hW,hx] at hξ
   have he₁:Envelope f':= Envelope.prodC _ _ (fun i hi=>(hw i hi).calls hz); have he₂:= he.mulC he₁; have hb' : Envelope q':= Envelope.prodC P (fun v=> backTo A N p hz (W v)) (fun i hi=> backTo_env _ _ _ _ ((hw i hi).calls hz)); have hb₀ : Envelope b':=Envelope.compactC (Complex.continuous_ofReal.comp (bare_cont _))
   have H (p : Finset I): Envelope (fineJob F p):= Envelope.prodC _ _ (fun i _=>hp.cost i)
   calc
    _ = ∫ W,L W+ K' W∂ prior G _ := by congr 1; funext W; change (_+_)*f' W=_; unfold L K'; unfold X S l; ring
    _ = (∫ W,V' W ∂prior G _)+ ∫ W,W' W ∂prior G _ := by rw [integral_add ((part_int hp.budget _).mul_bdd he₁.meas.aestronglyMeasurable (Eventually.of_forall he₁.cost.choose_spec)) ((part_int hp.budget _).mul_bdd he₂.meas.aestronglyMeasurable (Eventually.of_forall he₂.cost.choose_spec))]; exact congr_arg₂ (·+·) hs hξ
    _ = ∫ W, V' W+ W' W∂prior G _ := (integral_add (((hb₀.mulC (H _)).mulC hb').integrableC _) (((hb₀.mulC (H _)).mulC ((backTo_env A N p hz he).mulC hb')).integrableC _)).symm
    _ = _ := by
     congr 1; funext w; have he : a=insert b S := (by unfold S; rw [Finset.sdiff_singleton_eq_erase]; exact (insert_erase hv).symm)
     have hb:b∉ S:= fun ht=> (Finset.mem_sdiff.mp ht).2 (mem_singleton_self _); have hΩ (F'):fineJob F' a w=F' b w*fineJob F' S w:=by unfold fineJob; conv_lhs=> rw [he, prod_insert hb]
     change V' w + W' w = b' w*fineJob G' a w*q' w; unfold V' W';rw [hΩ,hΩ,show G' b=(F b+_) from Function.update_self .., hZ _ hb,Pi.add_apply]; ring
end Script
end YM.MergeProof.Ribbons.ManyCopies.Patrol
