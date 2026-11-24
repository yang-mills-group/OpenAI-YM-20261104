import YM.OPE.Compatible.Broma.Exhibit
/-!
# Angular convoy
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v v':ℝ}{C:KernelChoices}{P:Patch}{R:ChartRatio G}{p:Clip}{b:ℝ}
variable (B:Medal P G K.K P.J)(H:LocalRatio R)(hs:G.Simple)(S:Sailing T P p R b) (hp: Crest G P K.K m)(ht:Aware d τ)
include ht H hs
local notation "A!"=> season B H hs S ht
-- lowest by chamber
lemma lipX (x:Phase)(p:solar G d τ)(n:ℕ)(hh:∀ i<x,p.val i=0) :
    let V:= A! n p
    let U:= YangZ B H hs S ht 0 n p.val
    (∀ i<x, U i=0) ∧ (∀ i≤x,V.val i=U i) :=by
         intro V U; have hz:= deckB B S n; let R':= charmSeal B (S.U n).gear; let H':RollD (S.U n) R' R:=⟨hs,H,hz⟩; have hu(i:Phase)(hi:i<x): U i=0:=by
              unfold U YangZ; rw [actorA]; apply Finset.sum_eq_zero; intro j _; by_cases he:j<x; rw [hh j he,map_zero]; rw [show Drift.chamber _ _ _ _ _ _ _ _=0 from acceptZ 0 (S.U n) R' R H' ht i j (lt_of_lt_of_le hi (le_of_not_gt he))]; rfl
         refine ⟨hu,fun i hi=>?_⟩; change rebase G ht _ U i=_; by_cases hx:i=2; swap;· exact sail _ _ _ _ hx
         subst i; rw [sip,hu 0 (lt_of_lt_of_le (by decide) hi),map_zero,smul_zero,add_zero]
lemma collarH (x:Tracts G d τ)(n:ℕ)(i:Phase)(h:rare i x): rare i (culm B H hs S ht n x) ∧
     ((culm B H hs S ht n x) i).val=wagon (ship P (S.U n).gear) P.order_cut K.K G (d+i.val) (τ i) (x i).val:=by
          let y:= culm B H hs S ht n x; let p':=Fallix G ht K (S.U n).gear P.order_cut x; let v:=A! n p'; let q:= Fallix G ht K (S.U (n+1)).gear P.order_cut; have he:q y=v:= q.apply_symm_apply _; obtain ⟨hz,hx⟩:= starMark ht x _ P.order_cut i h (K:=K); have hb:∀ t < i,v.val t=0:=fun t hT=>(lipX B H hs S ht i p' n hz |>.2 t hT.le).trans (lipX B H hs S ht i p' n hz|>.1 t hT); have hv: rare i y:= receiving ht y _ P.order_cut i (show ∀ t < i,(q y).val t=0 from he.symm ▸ hb) (K:=K) -- t < i tokens
          refine ⟨hv,?_⟩; have hp : Mag P.J P.J:= (S.shot n).mag
          let D:= ship P (S.U n).gear; have hd:(S.U (n+1)).gear=D.land:= interlock P _ _ (S.shot n); let M:= lapD (atlasF G (S.U (n+1)).gear P.order_cut K.K) (τ i) (d+i.val); let C:= boostS (atlasF G (S.U (n+1)).gear P.order_cut K.K) (-(1/2:ℝ)) (τ i) (d+i.val); have hV: (q y).val i=C (y i).val:=(starMark ht _ _ P.order_cut i hv (K:=K)).2
          have hw: v.val i=YangZ B H hs S ht 0 n p'.val i:=(lipX B H hs S ht i p' n hz).2 i le_rfl; let t : Tower (Shade G) d τ:=p'.val; have hP:= deckB B S n; let W:=charmSeal B (S.U n).gear; let F:=sectorOp P K.K (S.U n) W R 0 (awareLeaf ht i) d i i hs hP H
          have hB:v.val i= F (t i):=by
               let H':RollD (S.U n) W R:=⟨hs,H,hP⟩; rw [hw]; change actor _ _ _ (0:ℝ) H' ht t i=_; rw [actorA,Finset.sum_eq_single i]; rotate_left
               · intro j _ hj; rcases lt_or_gt_of_ne hj with hx|hx; rw [show t j=0 from hz j hx,map_zero]; rw [acceptZ 0 _ _ _ H' ht i j hx]; rfl -- arity
               · simp
               unfold Drift.chamber; rw [dif_pos (le_refl _),reacquire]; rfl
          have hY:= invest D (S.U n) (S.U (n+1)) (by exact B) R hp (by rfl) hd hs 0 H i d -- need m+1
          -- τ i succ. Need depend output casts
          have hQ (m:ℕ)(hm:45≤m) (a:bed G (d+i.val) m): sectorOp P K.K (S.U n) W R 0 hm d i i hs hP H (warmEat (m:=m) a.val (atlasF G (S.U n).gear P.order_cut K.K))=warmEat (m:=m) (wagon D hp.2.1 K.K G _ _ a.val) (atlasF G D.land hp.2.1 K.K):=by
               cases m with | zero=>omega | succ m=> exact hY m hm _ a.property (by exact hP)
          apply (show Injective C from (show LeftInverse (boostS (atlasF G (S.U (n+1)).gear P.order_cut K.K) (1/2:ℝ) (τ i) (d+i.val)) C from fun x=> sustain ..).injective); rw [show C (y i).val=_ from hV.symm]; rw [he,hB]; set V:=x i; rw [show t i= _ from hx, show C=boostS (atlasF G D.land P.order_cut K.K) (-(1/2:ℝ)) (τ i) (d+i.val) from (by unfold C; rw [hd])]; exact hQ (τ i) (awareLeaf ht i) (x i)
end YM.OPE.Drift
