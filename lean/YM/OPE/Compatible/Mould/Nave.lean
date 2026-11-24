import YM.OPE.Compatible.Mould.Ring
/-! # Leading towel for stiffness kernels. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}
section Wick
-- upper boost equal
lemma bakeQL (A:RowB I)(t:ℝ)(x:Seat k m I)(h:x∈rooft I k m r)(hp:r ≤ i): lilies m k I (boostS A t m k x) i=lilies m k I x i:=by
      let T:Seat k m I→ₗ[ℝ]Seat k m I:=(lapD A m k).toLinearMap; let v(l:ℕ):= T^l; let g:=lilies m k I; rw [boostS,Hflow,map_sum,Finset.sum_apply,sum_eq_single 0]; rotate_left
      · intro j _ hj; rw[map_smul,Pi.smul_apply]; change _ • g (v j x) i=0; suffices H:g (v j x) i=0 by rw [H,smul_zero]
        have ht(z: Seat k m I)(hx:z∈rooft I k m r)(i:ℕ)(h:r ≤ i): lilies m k I (lapD A m k z) i=0:=by rw [pulse_i,hx (i+2) (by omega)]; ext1 l; simp [Script.pad,tunnel,Sack.rope]
        have he(q:ℕ): v q x∈rooft I k m r:=by induction q with | zero=>exact (by simpa [v])| succ n ih=> unfold v; rw [pow_succ', End.mul_apply]; exact fun i h=> ht _ ih i h.le
        cases j with| zero=>exact (hj rfl).elim| succ j=>unfold v; rw [pow_succ',End.mul_apply]; exact ht _ (he j) i hp
      · simp
      · simp
variable (hp:4≤ k)(X:Train k)(h:Aware d τ)
lemma boreX (p:Tracts G d τ):
      let P':=(Fallix G h K X hp p); (p 0).val= boostS (atlasF G X hp K.K) (1/2) (τ 0) (d+(0:Phase).val) (P'.val 0):=by
          intro P'; rw [show P'.val 0 = _ from (show ((Fallix G h K X hp p)).val 0= _ from (starMark (K:=K) h _ _ _ 0 (show rare 0 p from fun j hj=>by change j.val<0 at hj; omega)).2)]; exact Eq.symm (sustain ..)
lemma leaderX (p:Tracts G d τ)(hx:Variance.CapE r (Fallix G h K X hp p)) (hi:r ≤ i): lilies (τ 0) (d+(0:Phase).val) (Shade G) (p 0).val i= Variance.topX (Fallix G h K X hp p) i :=by
      let Q:=Fallix G h K X hp p; have ht: Q.val 0∈rooft _ _ _ r:= hx; exact (congr_arg (fun p=> lilies (τ 0) (d+(0:Phase).val) _ p i) (boreX hp X h p (K:=K))).trans (bakeQL _ _ _ ht hi)
end Wick
lemma trimBell {p:Script I r}(hp:Bells p k)(ht:l≤k): Bells p l:=fun i j hj=>hp i j (hj.trans_le ht)
lemma CropTide (p:Tracts G d τ)(hv:r≤ i)(h:Crop r p): (terrace G (d+(0:Phase).val) (τ 0) i (p 0))=0:=Subtype.ext (h i hv)
variable {w:ℝ} (D:Stern K P τ l d w)
noncomputable abbrev tag (e:ℕ) : Tracts G d τ→L[ℝ] Bead G l e:= (Drift.Turns D 0).Tap e ∘L ContinuousLinearMap.proj (0:Phase)
lemma tagX (p:Tracts G d τ)(he:e<l+1)(r:Fin (e+1)):
     tag D e p r= coordinateQ G l e r.val (Flume.Script.tiller G r.val (τ 0) (e-r.val) (by have ht:=sternCap D 0;omega) l (terrace G (d+(0:Phase).val) (τ 0) r.val (p 0))):=by
          unfold tag; rw [rope D 0 he]; rfl
abbrev LimitQ {k:ℕ}(x:Bead G l k)(n:ℕ):Prop:=∀ j:Fin (k+1), n ≤ j.val→ x j=0
lemma fringP (p:Tracts G d τ)(he:e<l+1)(hv:Crop r p): LimitQ (tag D e p) r:=by intro i hi; rw [tagX D p he,CropTide (r:=r) p hi hv,map_zero,map_zero]
end YM.OPE.Stroke
