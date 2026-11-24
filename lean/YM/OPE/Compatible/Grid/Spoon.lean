import YM.OPE.Compatible.Grid.Lamp
/-!
# Lifting into the pulse invariant Submodule
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Grid
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series ScriptJ GaussianScore Work.F05 Rill Glass Coin Pilot Radial Flock
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier
variable {G:Gauge}{s b U D:ℝ}{d r m k q:ℕ}
variable {p:Script (Shade G) k}
abbrev lance (p: Script (Shade G) k): Muse G:= fun i=> Shell.throw (timbre ships p (k + i.val))
lemma crib (G:Gauge) (k d q m:ℕ)(hp:k≤d)(hq:m+2*(k+2)≤q): ∃ Z:ℝ,0≤Z∧∀ (p:Script (Shade G) k) (b:ℝ), soot q p b→ Tide (lance p) d m (Z*b):=by
     have hh(i:Phase):m+2*(k+i.val)≤q:=by have h:=i.isLt; omega
     choose Z hz H using fun i:Phase=>paySpray G m q k _ (hh i); refine ⟨∑ i,Z i,Finset.sum_nonneg (fun i _=>hz i),fun p b h i=>?_⟩
     have hb:0 ≤ b:= Sack.coins h; refine ⟨fun j hj=>hubbub (by omega),fun j=>?_⟩ -- change Float
     by_cases ht:j=k+i.val
     · subst j; rw [show lance p i (k+i.val)=_ from Pi.single_eq_same ..]; exact Sack.tips (H i p b h |>.1) (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f:=Z) (fun i _=>hz i) (Finset.mem_univ _)) hb)
     rw [show lance p i j=0 from hubbub ht]; exact Sack.zero (mul_nonneg (Finset.sum_nonneg (fun i _=>hz i)) hb) _
variable {n:Side}
lemma plumb (x:Bid.Dir G n)(i:Cover× Axis)(z:Site n): indexS i (upl z (spool G n x))=x (z+wrap n i.1,axisEquiv i.2):=rfl
lemma plank (z:Site n)(x:Bid.Dir G n): lotU (upl z (spool G n x))=expandAt z (represent x):=by funext i; rw [show expandAt z (represent x) i= _ from Work.F03.represent_link x (wrap n i.1+z,i.2)]; unfold lotU; rw [plumb,add_comm];rfl
open Arc Asymptotics Essay
local notation "Lf"=>Tested.germ
lemma nestsL (h:soot q p b)(hp:k≤d)(hq:2*(k+2)≤q)(u:ℝ→Bid.Dir G n)(hu: Gael u)(z:Site n): (fun t:ℝ=> (t^k)⁻¹* testQ p (expandAt z (represent (t • u t)))-(inkM (lance p) d z (u t)).atK t)=O[Lf] gradeP 3:=by
     let Z:= ‖(trill u).s‖+1; obtain ⟨K,hk,H⟩:= priceSpin h hq Z (by unfold Z; positivity); let W(t:ℝ):= upl z (spool G n (u t)); have he(v:ℝ):Quiet (W v) 0:= ⟨‖spool G n (u v)‖,norm_nonneg _,fun i=> (norm_le_pi_norm (spool G n (u v)) (z+wrap _ i.1,i.2)).trans_eq (by unfold poise;ring)⟩
     refine Asymptotics.isBigO_iff.mpr ⟨K,?_⟩; filter_upwards [((Gael.oath hu).limit.norm.eventually (gt_mem_nhds (lt_add_one ‖(trill u).s‖))),Tested.eventually_pos] with t (hZ:‖u t‖<Z) (ht:0<t)
     let v:=u t; have hx:= H (W t) (he t) (fun i=>by unfold W; rw [plumb]; exact (norm_le_pi_norm (u t) _).trans hZ.le) t ht; rw [show lotU (t • W t)= expandAt z (represent (t • v)) from by rw [← plank, map_smul]; rfl] at hx
     have hy(i:ℕ)(hi:i<k):wholeX (timbre ships p i) (fun _=>W t) =0:=by
          rw [←(doReads h (by omega) _ (fun j:Fin i=> he t)).tsum_eq]; simp_rw [sifts_nil _ _ hi]; simp
     let A:= inkM (lance p) d z v; have he(i:Phase): wholeX (timbre ships p (k+i.val)) (fun _=> W t) = A.seq i.val:=by
          let T:= timbre ships p (k+i.val); let B:= lance p; change Flume.Script.value _ T _=_; rw [← throw_flair (I:=Shade G) (N:=n) (k:=d+i.val) (spool G n v) (show k+i.val≤d+i.val by omega) T z]; fin_cases i<;>rfl
     have hb: (∑ i∈Finset.range (k+3), t^i *wholeX (timbre ships p i) (fun _=>W t))= t^k*A.atK t:=by simp_rw [show k+3=k+2+1 from rfl]; rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_eq_zero (fun i hi=>show t^i*_ = 0 from by rw [hy i (Finset.mem_range.mp hi),mul_zero])]; rw [show wholeX (timbre ships p k) (fun _=>W t)=A.s from he 0,show wholeX (timbre ships p (k+1)) (fun _=>W t)=A.l from he 1,show wholeX (timbre ships p (k+2)) (fun _=>W t)=A.h from he 2]; unfold JetS.atK; simp only [smul_eq_mul]; ring
     rw [hb] at hx; let z':= testQ p (expandAt z (represent (t • u t))); change ‖(t^k)⁻¹*z' - A.atK t‖≤ K*‖t^3‖; rw [show (t^k)⁻¹*z'-A.atK t=(z'-t^k*A.atK t)/t^k from by field_simp, norm_div, Real.norm_of_nonneg (show 0≤t^k by positivity), Real.norm_of_nonneg (show 0≤t^3 by positivity), div_le_iff₀ (by positivity)]; exact hx.trans_eq (by ring)
lemma duly (h:soot q p b)(hp:k≤ d)(hq:2*(k+2)≤q)(hx:p.painted): Pathic d (lance p) :=by
      intro n z; refine ⟨meridian _ _ _ _ _ ((crib G k d q 0 hp (by omega)).choose_spec.2 p b h),fun {x y s} ht=>?_⟩; let g (t:ℝ):=t⁻¹ • x t; let f(t:ℝ):= t⁻¹ • y t
      have hG:Gael g:= Gael.walk _ ht.hX ht.gx; have hF:Gael f:=Gael.walk _ ht.hY ht.gy
      apply ((nestsL h hp hq f hF z).sub (nestsL h hp hq g hG z)).congr' _ Filter.EventuallyEq.rfl; filter_upwards [Tested.eventually_pos, ht.law.filter_mono (show Lf≤𝓝 0 from nhdsWithin_le_nhds)] with t (he:0<t) hP; have hz:= (Mar_ord .. |>.1 hP); simp only [f,g]; rw [smul_inv_smul₀ he.ne',smul_inv_smul₀ he.ne',← hz,expandAt_gauge, signalV p hx h]; ring
end YM.OPE.Cascade.Grid
