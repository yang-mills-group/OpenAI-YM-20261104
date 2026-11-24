import YM.OPE.Compatible.Frog.Dolls
/-!
# arced topology. zero slices and leading uses
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m l k:ℕ}{K:Sponsor G}{T:Seasons K}{v b:ℝ}
open Module
variable {τ:Char.Phase→ℕ}
local notation "T!"=> Tower (Shade G) d τ
lemma sequenceCL (u:ℝ→deck (Shade G) n)(h:Gael u)(i:Phase) (j:ℕ):∃ T:Pole (deck (Shade G) n) j→L[ℝ]ℝ,∀ p:Pole _ j, (trill (Tensor.diagonal p ∘ u)).seq i.val=T p:=by
      let f(p:Pole (deck (Shade G) n) j):= Tensor.diagonal p∘u
      have hv(p):Bond (Tensor.diagonal (p:Pole (deck (Shade G) n) j)):= Bond.multiline (A:=p) (w:=fun _ v=>v) fun _ y=>Bond.glyph y
      have he(p) : Reads (f p) (trill (f p)):= Gael.oath (Gael.climb _ (hv p) h)
      let T:Pole (deck (Shade G) n) j →ₗ[ℝ] ℝ:= {
           toFun p:=(trill (f p)).seq i.val
           map_add' x y:=by rw [show trill (f (x+y))=trill (f x)+trill (f y) from Gael.chooses ((he x).sum (he y))]; fin_cases i<;>rfl
           map_smul' a x:=by rw [show trill (f (a • x))=a • trill (f x) from Gael.chooses ((he x).smul a)]; fin_cases i<;>rfl }
      exact ⟨T.toContinuousLinearMap,fun _=>rfl⟩
lemma voicedCL (p:Site n)(v:Fin i→deck (Shade G) n): ∃ C:Seat k m (Shade G)→L[ℝ] ℝ, ∀ x:Seat k m (Shade G),C x=scribe p (lilies m k _ x i) v:=by
      let M:= reading m i p ∘L moduleAt m k i (Shade G); refine ⟨ContinuousMultilinearMap.apply ℝ _ _ v ∘L M,fun x=>?_⟩; exact (show _= _ from (show M x v=_ from (by unfold M; rw [ContinuousLinearMap.comp_apply,toScript]; exact (instruments _ (sootS ((sproutV m k x).2 i)) p v).tsum_eq.symm)))
lemma fluteCL (u:ℝ→Bid.Dir G n)(h:Gael u) (p:Site n)(q i:Phase): Continuous fun x:T! => (trill (fun t=>(inkM (spread G d τ x) d p (u t)).seq q.val)).seq i.val := by
     let U:=spool G n; let v:= U ∘u; have hU : Gael v:= Gael.up h U.toContinuousLinearMap; let F:=fun x:T! =>lilies (τ q) (d+q.val) (Shade G) (x q); let Q:=d+q.val
     let C (j:ℕ):T!→L[ℝ] Pole (deck (Shade G) n) j:= reading _ _ p ∘L moduleAt (τ q) Q j (Shade G) ∘L ContinuousLinearMap.proj q
     let f(x:T!)(j:ℕ):=Tensor.diagonal (C j x) ∘ v; have hx(t x j): f x j t= Flume.Script.value p (F x j) (v t):=by unfold f; change Tensor.diagonal (reading _ _ p _) _=_; rw [toScript]; exact (instruments _ (sootS ((sproutV _ _ (x q)).2 j)) p _).tsum_eq.symm -- tol
     let z(x:T!)(j):=trill (f x j); have he(p)(x):Bond (Tensor.diagonal (C p x)):= Bond.multiline (A:=C p x) (w:=fun _ v=>v) (fun _ l=> Bond.glyph l); have hf(x:T!)(j):Reads (f x j) (z x j):=Gael.oath (Gael.climb _ (he j x) hU)
     have hh(x:T!): trill (fun t=>(inkM (spread G d τ x) d p (u t)).seq q.val)=∑ j∈Finset.range (Q+1), z x j:=by
          simp_rw [vein_i,Flair]; rw [show (fun t=>_)= (∑ j∈Finset.range (Q+1),f x j) from ?_]; apply Gael.chooses; generalize Finset.range (Q+1)=P; induction P using Finset.induction_on with | empty=> simp only [Finset.sum_empty]; exact Reads.constants 0 | insert i s hi ih=> rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact (hf _ i).sum ih
          funext t; rw [Finset.sum_apply]; apply Finset.sum_congr rfl fun i _=> (hx t x i).symm
     choose C' H using fun j=> sequenceCL v hU i j; simp_rw [hh, Char.seqSum,show ∀ x:T!,∀ j,(z x j).seq i.val=C' j (C j x) from fun x j=> H j _]; apply continuous_finsetSum; exact fun t _=> (C' t).continuous.comp (C t).continuous
lemma mortal (p:Site n)(u:ℝ→ Bid.Dir G n)(h:Gael u)(i:Phase): Continuous fun x:T! => (mine (fun t=>inkM (spread G d τ x) d p (u t))).seq i.val:=by
     let U x t:= inkM (spread G d τ x) d p (u t); let V(x:T!)(j:Phase):=trill (fun t=>(U x t).seq j.val); have he(i j:Phase): Continuous (fun x:T! =>(V x j).seq i.val):= fluteCL u h _ _ i
     have hz(x:T!): mine (U x) = assembleJ (V x 0) (V x 1) (V x 2):=by
          have hk:Fitted (U x):= Fitted.arose u _ h (meridian _ _ 0 _ _ (resin x fun i=>Nat.zero_le _)); exact Fitted.totals (Gael.oath hk.A) (Gael.oath hk.B) (Gael.oath hk.C)
     change Continuous fun x:T! =>(mine (U x)).seq i.val; simp_rw [hz]
     have h1(j:Phase):Continuous (fun x=>(V x j).s):=he 0 j; have h2(j:Phase):Continuous (fun x=>(V x j).l):=he 1 j; have h3(j:Phase):Continuous (fun x=>(V x j).h):=he 2 j
     fin_cases i<;>norm_num [JetS.seq,assembleJ,ski]<;>fun_prop (disch:= assumption)
end YM.OPE.Drift
