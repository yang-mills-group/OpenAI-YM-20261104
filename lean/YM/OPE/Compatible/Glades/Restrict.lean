import YM.OPE.Compatible.Glades.Belief
/-! Restrict focused marker set (to Bud). Only Tow witnessed; no claims about budget for production along the same path unless all mode costs still centered. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Mirror
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi Finset
open Ribbon MeasureTheory Push.GridApprox.Nil
open scoped Topology Classical
variable {X V I J :Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
   {G:Gauge} {n:Side}{R:Rep G n}
variable (e:V ↪ I){t:ℝ}
lemma trim_borne {o:I→Site n}{f:Config G n→Words I}{S:Support n}(h:Borne o S f t): Borne (o ∘ e) S (trim e∘ f) t:=by
   refine ⟨fun U V he hp=>congr_arg (trim e) (h.home _ _ he hp), fun _ _=>congr_arg (trim e) (h.turns ..),fun i=>h.me _,fun U m hm=>?_⟩
   refine h.scope U (imageM e m) ?_; by_contra hh; apply hm; simp [imageM] at hh; intro i hi; exact hh hi -- inspect
lemma trim_pad {o:I→Site n}{H:Support n→ Config G n→Words I}{K:Box n→ Config G n→ Words I}(h:Carton o H K t):Carton (o∘ e) (fun i=> trim e∘ H i) (fun i=> trim e∘ K i) t:=by
   have hp {f:Words I}(h:Accent.rises f): Accent.rises (trim e f):=by
       intro i hi; have ht := Finset.card_image_of_injective i.val e.injective; exact ht ▸ h _ hi
   constructor
   · intro i; obtain ⟨hh,ht⟩:=h.exp i
     refine ⟨⟨trim_borne e hh.toBorne,fun i hi=>hh.permits i (fun h=>hi ((congr_arg _ h).trans (map_zero (trim e)))),fun i'=>?_⟩,fun _=> hp (ht _)⟩
     change (H i i').part (imageM e _)=_; rw [heat_quiet]; exact hh.sil i'
   intro i; obtain ⟨hh,ht⟩:= h.flag i; exact ⟨⟨trim_borne e hh.toBorne,fun i hi=> hh.permits i (fun h=>hi ((congr_arg _ h).trans (map_zero (trim e))))⟩,fun _=>hp (ht _)⟩
lemma trim_towed {o:I→ℝ}{H:J→X→Words I}{S:J→Support n}{m:ℕ}{a:ℝ}(h:Towed o S H m a t)(hp:∀ i,0 < o i): Towed (o∘e) S (fun i=>trim e ∘ H i) m a t:=by
   obtain ⟨Q,hq,hs,he⟩:=h; refine ⟨Q,hq,hs,fun i=>?_⟩; obtain ⟨v,hv,hy,hS⟩:= he i
   refine ⟨fun i=>v (imageM e i),fun i=> hv _,fun U i=>hy ..,le_trans ?_ hS⟩
   unfold wordsPrice; let R:Finset (Mode I):= univ.image (imageM e)
   refine le_trans (?_ : _ ≤ ∑ i∈ R,_) (sum_le_sum_of_subset_of_nonneg (subset_univ R) (fun i _ _=>mul_nonneg (Poly.worth hp _|>.le) (hv _))) -- inspect
   unfold R; rw [sum_image (LeftInverse.injective (tall e)|>.injOn)]; apply sum_le_sum; intro i hi; have ht:Poly.toll (o∘e) i=Poly.toll o (imageM e i):=by unfold Poly.toll imageM; rw [prod_image e.injective.injOn]; rfl
   change Poly.toll (o∘e) i*v _ ≤ Poly.toll o _*_; rw [ht]
lemma trims_mulPass (p:Words I)(hp:p.part (Bud I).quiet=0): trim e (Poly.pass p)=Poly.pass (trim e p):=by
   apply passM (trim e) (low_one _) (trims_mul e) p hp; change p.part (imageM _ _)=_; rw [heat_quiet]; exact hp
lemma pardon (B:Census V)(f:V→ℂ)(s:B.Mode) : (Mach B f).part s=∑ v:V,if s=B.fire v then f v else 0:=by unfold Mach; rw [Poly.part_sum]; simp only [Poly.part_send]
lemma lowM (f:I→ℂ) : trim e (Mach (Bud I) f)=Mach (Bud V) (f ∘ e):=by
   unfold Mach
   let F:=univ.image e; rw [map_sum, ← sum_subset (subset_univ F) (fun i hi h=>?_),show F=univ.image e from rfl,sum_image e.injective.injOn]; refine sum_congr rfl fun i hi=>?_
   · rw [loose]; have hh: warm e ((Bud I).fire (e i)):= by rw [← heat_fires]; exact heat_image ..
     rw [if_pos hh,← heat_fires,tall]; rfl
   rw [loose,if_neg]; intro hh; obtain ⟨v,hv⟩:= (heat_iff ..).1 hh _ (mem_singleton_self _); exact h (hv ▸ mem_image_of_mem e (mem_univ v))
lemma low_bar (R: Activities G n)(U:Config G n)(p:Box n): trim e (bar R (Bud I) U p)= bar R (Bud V) U p:=by
   change trim e (Poly.send (Bud I).quiet _) = _; rw [loose]; simp_rw [← heat_quiet e]; rw [if_pos (heat_image ..), tall]; rfl
lemma kiosk {o:I→Site n}{F:I→ Config G n→ℂ}{K:I→Box n→ Config G n→ℂ}
    {A: Config G n→Words I}{w:I→ℝ}{x:ℝ}(h:Served R F K A o w x t)(hp:∀ i,0<w i):Served R (F∘e) (K∘e) (trim e∘ A) (o∘e) (w∘e) x t:=by
   obtain ⟨H,S,hC,hT,hY,rfl⟩:=h; refine ⟨_,_,trim_pad e hC,trim_towed e hT hp,trim_towed e hY hp,?_⟩
   funext U; unfold restore; rw [comp_apply,map_smul,trims_mul,trims_mulPass,map_add, map_sum,lowM, field_map (trim e) (low_one _) (trims_mul e)]; simp_rw [map_add,low_bar,lowM]; rfl
   rw [Poly.part_plus,mute,Poly.part_sum,zero_add]; exact sum_eq_zero fun i _=> (hC.exp i).1.sil _
end YM.MergeProof.Ribbons.ManyCopies.Mirror
