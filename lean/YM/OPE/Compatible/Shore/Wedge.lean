import YM.OPE.Compatible.Shore.Sings
/-!
# Restrictions from a signed foreground
For witness of one v cell propagation testing away from its center we
use only its part, despite that no Harmony for another base is presently
known. May take full projection to compare root later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Mirror
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open scoped Topology BigOperators Classical
variable {V I J W X : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype W][DecidableEq W]{G:Gauge}{n : Side}{H:RG.History G}(e:V ↪ W)
lemma narrower {p k N i:ℕ}{y:Config G (H.S.side k p)→Words W}(h:Integrable y (prior G _))(ht:i≤k) : trim e ∘ gust H N p k y i ht= gust H N p k (trim e ∘ y) i ht:=by
   induction ht using Nat.decreasingInduction with
   | self=> rw [gust_base,gust_base]
   | of_succ i hi ih=>
      rw [gust_step _ _ _ _ _ hi,gust_step _ _ _ _ _ hi, ← ih]; funext v; let Z:=(trim e).toContinuousLinearMap.restrictScalars ℝ; change Z _=_; unfold StepData.push; have he:= Z.integral_comp_comm (StepData.push_slice (H.levels.transition_mass i p (H.β N p (i+1))) v _ (gust_live H N _ _ _ h hi)); simp_rw [ContinuousLinearMap.map_smul] at he; exact he.symm
lemma station (R:Rep G n)(f:W→ Config G n→ℂ): trim e ∘ birth (Bud W) R f=birth (Bud V) R (f∘e):=by
   funext U; unfold birth; rw [Function.comp_apply,map_smul]; rw [trims_mulPass e _ (mute ..),lowM]; rfl
-- dot on full V subset. horizontal
variable (I)
def limb : (V×I) ↪ W×I:= Function.Embedding.prodMap e (Function.Embedding.refl I)
variable {I}{P:Ensemble V}{P':Ensemble W} (h:Screenlet P P' e)
local notation "b" => limb I e
include h
lemma limb_focus {p: Mode (V×I)}(hp:Focused P.v p): Focused P'.v (imageM (limb I e) p):=by
   -- correct order
   rw [← district_iff] at hp ⊢; intro i hi; obtain ⟨i,hv,rfl⟩:=mem_image.mp hi; change e i.1=P'.v; exact (congr_arg e (hp hv)).trans h.start
lemma limb_drum (i:V)(p:Mode (V×I)):imageM (limb I e) (drum (P.perms i) p)=drum (P'.perms (e i)) (imageM (limb I e) p):=by
    apply Subtype.ext; simp only [imageM,drum,pares,image_image]; refine image_congr (fun j _=> Prod.ext ?_ rfl); exact (congr_fun (h.runs i) _).symm
lemma wedge {R:Rep G n}{o:W×I→Site n}{F:W×I→ Config G n→ℂ} {g: W×I→ Box n→ Config G n→ℂ}{Y: Config G n→Words (W×I)}{v:W×I→ℝ}{c u:ℝ}{y:W→ Site n} (hS: ManyCopies.Serves R F g Y P'.v P'.move y P'.perms o v c u)(hz:∀ i,0<v i):
    let r:= limb I e
    ManyCopies.Serves R (F∘r) (g∘r) (trim r∘Y) P.v P.move (y ∘ e) P.perms (o∘r) (v∘r) c u:=by
    intro r; obtain ⟨Q,Z,hC,hT,hk,hX,rfl⟩:=hS
    refine ⟨_,_,trim_pad r hC, trim_towed r hT hz,trim_towed r hk hz,fun i hi=>⟨P.to_ref i,fun U=> ?_⟩,?_⟩
    · have he:= (hX (e i) (by rw [← h.start]; exact e.injective.ne hi)).2 U; rw [← show P'.move (e i)= _ from congr_fun h.acts i]; dsimp only [Function.comp_apply]; exact ⟨fun j p hp=> (congr_arg _ (limb_drum e h i p)).trans (he.1 _ _ (limb_focus e h hp)), fun j p hp=> (congr_arg _ (limb_drum e h i p)).trans (he.2 _ _ (limb_focus e h hp))⟩
    funext U; unfold restore; rw [Function.comp_apply,map_smul,trims_mul,trims_mulPass,map_add,map_sum,lowM,field_map (trim r) (low_one _) (trims_mul r)]; simp_rw [map_add,low_bar,lowM]; rfl
    rw [Poly.part_plus,mute,zero_add,Poly.part_sum]; exact sum_eq_zero fun i _=>(hC.exp i).1.sil U
lemma wedged {R:Rep G n}{U:I→ Stem W G n}{F: Config G n→ Words (W×I)}{o:W→Site n}{χ:Guard (Names W I)}{χ':Guard (Names V I)}{v:I→ℝ}{m:ℝ}
    (hx:Owned χ R o P' U v m F)(hK:∀ i,χ'.safe i→χ.safe (imageM (limb I e) i)):
    Owned χ' R (o∘e) P (fun i=>cropStem e (U i)) v m (trim (limb I e)∘ F):=by
    obtain ⟨Z,hH,hY,hT⟩:= hx.issues
    let Q:=trim (limb I e)∘Z; refine ⟨Q,?_,fun U s hs=> hY U _ (hK s hs),⟨fun i=> (hT.earned i).high e h,hT.way,?_⟩⟩
    · exact ((trim (limb I e)).toContinuousLinearMap.restrictScalars ℝ).integrable_comp hH
    exact wedge e h hT.ship (fun i=>hT.way i.2)
end YM.MergeProof.Ribbons.ManyCopies.Mirror
