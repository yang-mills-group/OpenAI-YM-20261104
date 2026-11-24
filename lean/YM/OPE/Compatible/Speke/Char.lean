import YM.OPE.Compatible.Speke.Cube
/-!
# CutScene trigon. power-no-log through any reading. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nestle
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
open Balsam Port Extra.FD.OPE
variable {U:Gloam}{d c s:ℝ}{p q t:Pose}{x y z:Crew U}{B:Finset (Crew U)}{K:ℕ→ℕ}{J:Zem}{X Y Z:Candidate U}
lemma auction (Pred:Crew U→ℝ→Prop)(B:Finset (Crew U))(h:∀ i,∃ a>0,Pred i a)(hp:∀ i a b, 0 < b → b ≤ a→ Pred i a→Pred i b):∃ a>0,∀ i∈B,Pred i a:=by
   induction B using Finset.induction_on with
   | empty=> exact ⟨1,by norm_num,by simp⟩
   | insert i B hi ih=>
     obtain ⟨a,ha,H⟩:=ih; obtain ⟨b,hb,h⟩:=h i; refine ⟨min a b,lt_min ha hb,fun j h=>?_⟩; obtain rfl|he:=Finset.mem_insert.mp h; exact hp _ _ _ (lt_min ha hb) (min_le_right ..) ‹_›; exact hp j _ _ (lt_min ha hb) (min_le_left ..) (H j he)
-- transport
private lemma transported (b:Crew U)(i:ℕ)(he:2*K i<(U.M i).val)(a u:Axis): (∑ x∈ rush K b i,mx X Y Z J a u i x)=cubic K J (peekX b X) (peekX b Y) (peekX b Z) a u i:=by
     unfold rush mx cubic; rw [Finset.sum_image (by intro x h y h' hx; exact rumSort b i he h h' hx)]; apply Finset.sum_congr rfl; intro p _; rw [cup_crystal,cup_crystal,cup_crystal]
abbrev win (p q t:Pose):=p.heat+q.heat+t.heat
open Pose
lemma comic (H:∀ᶠ i in atTop,Even (U.M i).val)(x y z:Crew U)(p q t:Pose)(hp:Vener J c): Fruit U (win p q t) (Nestle.hash (vote p x) (vote q y) (vote t z) J) 0:=by
     let B:Finset (Crew U):={x,y,z}; have hx:x∈B:=by simp only[B];simp
     have hy:y∈B:=by simp only[B];simp
     have hz:z∈B:=by simp only[B];simp
     let X:=vote p x; let Y:=vote q y; let Z:=vote t z; let m:=win p q t; obtain ⟨d,hd,hD⟩:= auction (fun i a=> Cohort U a (peekX i X) (p.heat+1)) B (fun b=>cop H b p x) (fun i a b ht hy he=>scorch he ht hy); obtain ⟨u,hu,hU⟩:= auction (fun i a=> Cohort U a (peekX i Y) (q.heat+1)) B (fun b=>cop H b q y) (fun i a b ht hy he=>scorch he ht hy); obtain ⟨v,hv,hV⟩:= auction (fun i a=> Cohort U a (peekX i Z) (t.heat+1)) B (fun b=>cop H b t z) (fun i a b ht hy he=>scorch he ht hy)
     let s:=min (min d u) v; have hS:0<s:=lt_min (lt_min hd hu) hv; obtain ⟨K,L,LG⟩:= guide B hS; let Q(b:Crew U):= Triad K J (peekX b X) (peekX b Y) (peekX b Z); let F(a:PlaqAxes)(i:ℕ):=∑ w∈ RimC B K i, mx X Y Z J a.val.1 a.val.2 i w; have hMo :m+4=p.heat+1+1+(q.heat+1)+(t.heat+1):=by unfold m win; omega
     have A(i:Crew U)(h:i∈B):Fruit U m (Q i) 0:=by
           have hb:=scorch (hD i h) hS (le_trans (min_le_left ..) (min_le_left ..)); have hr:=scorch (hU i h) hS (le_trans (min_le_left ..) (min_le_right ..)); have ht:=scorch (hV i h) hS (min_le_right ..); exact charity L hp hS hb hr ht hMo
     have T(a:PlaqAxes):Fruit U m (F a) 0:= remote L.station hx hy hz _ _ hMo
     change Fruit U m (Nestle.hash X Y Z J) 0; rw [show Nestle.hash X Y Z J=(∑ i∈B,Q i)+∑ a,F a from ?_,←add_zero (0:ℝ)]
     · exact Fruit.sum (show _ from (by simpa only [Finset.sum_const_zero] using Fruit.line B Q (fun _=>0) A)) (by simpa only [Finset.sum_const_zero] using Fruit.line Finset.univ F (fun _=>0) (fun i _=>T i))
     funext k; unfold Nestle.hash Q Triad; simp_rw [Pi.add_apply,Finset.sum_apply]; rw [Finset.sum_comm (s:=B),← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun a _=>?_); unfold F; simp_rw [fun u=> Eq.symm (transported u k (LG k|>.1) (J:=J) (X:=X) (Y:=Y) (Z:=Z) a.val.1 a.val.2)]; rw [←Finset.sum_biUnion (show (B:Set _).PairwiseDisjoint (fun x=>rush K x k) from fun x hx y hy he=> (LG k|>.2) x hx y hy he), add_comm, Finset.sum_sdiff (Finset.subset_univ _)]
end YM.OPE.Nestle
