import YM.OPE.Compatible.Chain.Roller
/-!
# No image copies of a potential marker in singular local curl legs. But far image terms survive. Estimates before each stationary launch.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Terp
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script Finset Metric
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent Further.FreeCovariance.KP GaussianScore Work.F06 Work.F08
local notation "M" => TypeFace 1
variable {C:KernelChoices}{r:ℕ} (H:Even n.val)
omit H in
def letter (X:Row M M)(x:Body 1 n)(q:edgeV n)(k:Kv):= if (axisK k).flip q.2 then -lineC X n (addressR (ferry k q)) x else lineC X n (addressR (ferry k q)) x
def boostJet (h:4≤ r)(v:Train r)(C:KernelChoices)(i j:G.ColorIndex)(p q:edgeV n):ℝ:= (boost H v h C).wick (MarkC H i (addressR p)) (MarkC H j (addressR q))
lemma pages (h:4≤r)(v:Train r)(a b:G.ColorIndex)(p q:edgeV n): boostJet H h v C a b p q=if b=a then ∑ k:Kv,letter (ShellRow C v) (addressR p) q k else 0 := by
       unfold boostJet; rw [boostFleet]; split
       next hh=>
            unfold acrossH; rw [Finset.sum_apply]; apply Finset.sum_congr rfl; intro k _; rw [stemR]; unfold letter; rw [Matrix.mulVec_single_one];rfl
       rfl
-- evaluate lag wraps from any origin; use characters incl frame at base
omit H
variable {W:Type*}{l: Filter W}{I:W→ Side}{U:(i:W)→Site (I i)}
def portAt (u:Site n)(i:edgeV n):edgeV n:=(u+i.1,i.2)
def warpAt (u:Site n)(x:Edge Cover):edgeV n:=(u+wrap n x.1,x.2)
abbrev horizon (v:Train r)(C:KernelChoices)(h:4≤r)(a b:G.ColorIndex)(x y:Edge Cover):= if b=a then Spill C v h (coord y.2) (coord x.2) (x.1-y.1) else 0
variable (U) (H:(i:W)→Even (I i).val)(hp:Tendsto (fun i=>(I i).val) l atTop)
include hp
lemma images_gone (u v:Edge Cover)(k:Kv)(ht:k≠0) : Tendsto (fun i=>separation (ferry k (warpAt (U i) v)).1 (warpAt (U i) u).1) l atTop:=by
      let C:= size v.1+size u.1+1
      apply Filter.tendsto_atTop.2; intro q; filter_upwards [hp.eventually (eventually_ge_atTop ((q+C)*2))] with i hi
      let x:=warpAt (U i) v; let y:=warpAt (U i) u; have hV : separation x.1 y.1≤ size v.1+size u.1:= by
           unfold separation x y warpAt; simp only; rw [add_sub_add_left_eq_sub,sub_eq_add_neg]; apply (pdist_triangle ..).trans; rw [pdist_neg]; exact Nat.add_le_add (within_size ..) (within_size ..)
      have hd: separation (decks k x.1) (ferry k x).1 ≤ 1 := by
           unfold ferry Step.used; split; next he=> simp only [separation,sub_sub_cancel]; rw [← wrap_step]; refine (within_size (step _) _).trans ?_; unfold size; simp [apply_ite (f:=Int.natAbs)] -- ignore  (I i)
           next he=>simp
      have hz : separation (ferry k x).1 x.1 ≤ separation (ferry k x).1 y.1+ separation x.1 y.1:= by rw (occs:=.pos [2]) [separation_comm]; simpa only [separation_comm x.1 y.1,separation_comm y.1 (ferry k x).1] using separation_triangle (ferry k x).1 y.1 x.1
      change (q+C)*2 ≤ (I i).val at hi; have he:=separation_triangle (decks k x.1) (ferry k x).1 x.1; have ht:= deck_free k ht x.1
      change q ≤ separation (ferry k x).1 y.1; unfold C at hi; omega
lemma pays (h:4≤r)(v:Train r)(a b:G.ColorIndex)(x y:Edge Cover): Tendsto (fun i=> boostJet (H i) h v C a b (warpAt (U i) x) (warpAt (U i) y)) l (𝓝 (horizon v C h a b x y)):=by
       simp_rw [pages]; unfold horizon; split;swap
       · exact tendsto_const_nhds
       let X:= ShellRow C v; let t:= Spill C v h (coord y.2) (coord x.2) (x.1-y.1)
       let f(k:Kv) := if k=0 then t else 0
       rw [show Spill C v h (coord y.2) (coord x.2) (x.1-y.1)=∑ k:Kv,f k from by unfold f; simp; rfl]
       apply tendsto_finsetSum univ; intro k _; by_cases hg:k=0
       · subst k; simp only [letter,axisK_id,Signed.one_flip,Bool.false_eq_true,if_false,ferry_0,f,if_true]; apply Tendsto.congr' (f₁:=fun i=>vein v C (coord y.2) (coord x.2) (x.1-y.1) _ ((warpAt (U i) y).1)) _ (old_coin hp v h ..); filter_upwards with i; unfold vein warpAt; simp only; rw [show _= _ from (show ((U i+wrap _ y.1)+wrap _ (x.1-y.1):Site (I i))=U i+wrap _ x.1 from by rw [map_sub]; abel)]; rfl
       unfold f letter; rw [if_neg hg]; simp_rw [show ∀ i, addressR (ferry k (warpAt (U i) y))=((ferry k (warpAt (U i) y)).1,coord y.2) from fun i=>by rw [show ∀ p:edgeV (I i),addressR p=(p.1,coord p.2) from fun _=>rfl,ferry_axis];rfl]
       have hz:= old_fars (C:=C) hp v h (coord y.2) (coord x.2) _ _ (images_gone U hp x y k hg)
       cases he:(axisK k).flip y.2
       · simp only [warpAt,he,Bool.false_eq_true, if_false]; exact hz
       simp only [warpAt,he,↓reduceIte]; simpa only [neg_zero] using! hz.neg
end YM.OPE.Cascade.Terp
