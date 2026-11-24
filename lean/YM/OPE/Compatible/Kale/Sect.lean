import YM.OPE.Compatible.Weave.Hub
import YM.OPE.Compatible.LevelX.Ela
/-! # Finite leaders over the measured quotient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e t:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v v':ℝ}{C:KernelChoices}{P:Patch}{R:ChartRatio G}{p:Clip}{b:ℝ}
-- finite bounds tilt
lemma plusA {p q:Script I r}(h:Brief p)(hx:Brief q): Brief (p+q):=by
   obtain ⟨s,hs⟩:=h; obtain ⟨t,ht⟩:=hx; refine ⟨s∪t,fun i h=>?_⟩; rw [Pi.add_apply,hs _ (fun hb=> h (mem_union_left _ hb)),ht _ (fun hb=> h (mem_union_right _ hb)),add_zero]
lemma scape (x:ℝ){p:Script I r}(h:Brief p):Brief (x • p):=by obtain ⟨t,H⟩:=h; exact ⟨t,fun i hi=>by rw [Pi.smul_apply,H i hi,smul_zero]⟩
lemma finA (s:Finset J)(p:J→Script I r)(h:∀ i∈s,Brief (p i)): Brief (∑ i∈s,p i):=by induction s using Finset.induction with | empty=> rw [Finset.sum_empty]; exact blankV| insert i t hp ih=> rw [Finset.sum_insert hp]; exact plusA (h i (mem_insert_self ..)) (ih (fun v hv=>h _ (mem_insert_of_mem hv)))
lemma lapBr {p:Script I (r+2)}(x: RowB I)(h:Brief p):Brief (Flume.Script.pad x.val p):=by
   obtain ⟨v,hv⟩:= h; refine ⟨v.image melt,?_⟩; intro i hi; unfold Flume.Script.pad Sack.rope; rw [show (fun i=>_)= fun i=> (0:ℝ) from ?_]; simp; funext j; split
   next he=> unfold tunnel; rw [hv,zero_mul]; intro h; exact hi (mem_image.mpr ⟨_,h,he⟩)
   rfl
lemma timbreB {p:Script (Shade G) r} (h:Brief p): Brief (timbre ships p k):=by
   obtain ⟨s,H⟩:=h; refine ⟨s.biUnion (fun i=>rim (ships i) k),?_⟩; intro i hi; unfold timbre; rw [show (fun i=>_)= fun i=> (0:ℝ) from ?_]; simp; funext j; by_cases he:j∈s
   · rw [stair (ships j) (fun hb=>hi (mem_biUnion.mpr ⟨j,he,hb⟩)),mul_zero]
   rw [H j he,zero_mul]
lemma settle {p: Seat k m I} (h: Prairies.visit p)(b:ℝ)(J:RowB I): Prairies.visit (boostS J b m k p):=by
   have he(i:ℕ): Prairies.visit (((lapD J m k).toLinearMap^i) p):=by
      induction i with
      | zero=> simpa
      | succ i ih=> rw [pow_succ',Module.End.mul_apply]; intro j; change Brief (lilies m k I (lapD J _ _ _) _); rw [pulse_i]; exact scape _ (lapBr J (ih _))
   intro i; rw [boostS, Hflow,map_sum,Finset.sum_apply]; apply finA; intro j _; rw [map_smul, Pi.smul_apply]; exact scape _ (he _ i)
lemma singleA {p:Script I r}(h:Brief p)(j:ℕ): Brief (Shell.throw p j):=by
   by_cases hp:j=r; subst j; rw [show Shell.throw p r=p from Pi.single_eq_same ..]; exact h
   rw [hubbub hp]; exact blankV
abbrev twilight (x:Tower (Shade G) d τ):Prop:=∀ i j, Brief (spread G d τ x i j) -- overload
lemma claimV (G:Gauge)(h: Aware d τ)(i:Phase)(p:bed G (d+i.val) (τ i))(hv:Prairies.visit (m:=τ i) p.val): twilight (ascendF G h i p):=by
    intro j a; rw [Drift.pick, baby]; simp_rw [Finset.sum_apply]; apply finA; intro k _; unfold Drift.glide; split; · exact blankV
    exact singleA (timbreB (hv k.val)) _
lemma conforms (x:Tracts G d τ)(p:Train r)(h:Aware d τ)(hp:4 ≤ r)(hx:∀ i:Phase, Prairies.visit (x i).val): twilight (Fallix G h K p hp x).val:=by
     let Z:= Larix G p hp K.K h (-(1/2:ℝ)) x; have hv (i:Phase):= claimV G h i (Z i) (show Prairies.visit _ from ?_); swap
     · rw [show (Z i).val=_ from lavaX G h (-(1/2:ℝ)) p hp x i (C:=K.K)]; exact settle (hx i) _ _
     intro i j; change Brief (spread G d τ (relief G h Z).val i j); let F: solar G d τ →ₗ[ℝ] Muse G:= (Drift.spread G d τ) ∘ₗ (solar G d τ).subtype; change Brief (F (Drift.relief G h Z) i j); rw [Drift.relief, _root_.sum_apply,map_sum,Finset.sum_apply,Finset.sum_apply]; exact finA _ _ (fun k _=> hv k i j)
lemma mirrorVisit (x:Tower (Shade G) d τ)(hp:twilight x)(a:Axis): twilight (Mirror a G d τ x):=by
    intro i j; rw [sunward]; obtain ⟨S,hS⟩:=hp i j; refine ⟨S.image (plusa a),?_⟩; intro z hz; unfold shapeR; rw [hS,mul_zero]; exact fun h=>hz (mem_image.mpr ⟨_,h,twinS ..⟩)
end YM.OPE.Quit
