import YM.OPE.Compatible.Bust.Gip
/-!
# τ Ward Gauge Response. canonical raw.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Paver
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m:ℕ}
variable {K:Sponsor G}{T:Seasons K}{v b:ℝ}
variable (P:Patch)(C:KernelChoices) (U:Boxes G P C) (A:Alps K T i v) (V:ChartRatio G)
noncomputable abbrev bow (p:Curtain I): Curtain I:= fun i=> bouquet (p i)
abbrev sculpt (b:ℝ)(X:Muse G)(d:ℕ): Muse G:= fun p:Phase=> bow (rushS P C A b U V X d p)
lemma beagle {m d:ℕ} (X:Curtain I){b:ℝ}(h:Volume X d m b): Volume (bow X) d m b:=⟨fun i hi=>by unfold bow; rw [h.1 i hi]; ext1 j; simp [bouquet,swing,Finset.sum_apply],fun i=> adjusted (h.2 i)⟩ -- sum ambiguous
lemma bustDD (X:Muse G)(v b:ℝ)(p: Site c) (h:Tide (rushS P C A b U V X d) d m v): inkM (sculpt P C U A V b X d) d p=inkM (rushS P C A b U V X d) d p:=by
     let q:= rushS P C A b U V X d; funext t; let L:=spool G c t; have he (r:ℕ)(i:Phase): Flair (bow (q i)) r L p= Flair (q i) r L p:=Finset.sum_congr rfl fun j _=> scoring _ (sootS ((h i).2 j)) _ _
     apply JetS.eta; exact he _ 0; exact he _ 1; exact he _ 2
def Paid (m k d:ℕ)(w b:ℝ): Prop :=∀ n:Side,let S:=subStud P C n; let he:=P.odd_side
                                         ∀ L g, licensed S he U A.clip A.live L A.sky g→∀ (t:S.Choices)(Z:FibreRep S he U t A g b)(p: Site n) (X:Muse G) (B:ℝ), Tide X d m B→ Tide (sculpt P C U A V b X d) d m (w*B)∧∀ x:Bid.Dir G n,∀ i:Phase, Mold ((TracePay S he U A t g V d X b p Z x).seq i.val) ((inkM (sculpt P C U A V b X d) d p x).seq i.val) (w*B*(1+‖spool G n x‖)^glideZ d) n k
lemma liquidity (hs:G.Simple)(ht:LocalRatio V)(hc:j+44≤m)(b:ℝ): ∃ w:ℝ,0 ≤ w∧ Paid P C U A V m j d w b:=by
      obtain ⟨s,D,h,hK,hD⟩:= spineP P C U; obtain ⟨c,hp,hm⟩:= costsS _ _ P hs hc s D h hK K T V ht C i d; obtain ⟨z,hz,H⟩:= gaV P C A V b m; refine ⟨c*z^5,by positivity,fun n L g ho t Z p X B hb=>?_⟩; have he:= hm n U (show Telet P U s D from ⟨hD.1,hD.2.1,hD.2.2.1,hD.2.2.2⟩) v b A L g ho t Z p X B hb z hz H; rw [bustDD P C U A V X _ b p he.1]; exact ⟨fun i=>beagle _ (he.1 i), he.2⟩ -- scope quant
lemma established (b:ℝ)(hs:G.Simple){i':ℕ}{w:ℝ}(hz:Paid P C U A V m i' d w b)(hk:Era U A)(X:Muse G)(r:ℝ)(h:Tide X d m r): Tide (sculpt P C U A V b X d) d m (w*r) :=by
      obtain ⟨N,hN⟩:= hk.bind; let n:Side:= ⟨N+1,Nat.succ_pos _⟩; obtain ⟨L,g,hg⟩:= hN n (Nat.le_succ _); let S:= subStud P C n; let t:S.Choices:= Classical.arbitrary _; obtain ⟨Z⟩:= enrol S P.odd_side U t hg b hs; exact (hz n L g hg t Z 0 X r h).1 -- Turn spots
-- pure uniqueness ∞
lemma scoreF {I:Type} [Fintype I] (p q:Curtain I) (hp:Volume p d m b){v':ℝ}(hq:Volume q d m v')(hx:∀ i:ℕ,sorted (p i))(hy:∀ i, sorted (q i)) (he:∀ n:Side,∀ u:deck I n, Flair p d u 0=Flair q d u 0): p=q:=by
     funext i; by_cases hv:i≤d; swap; · rw [hp.1 _ (not_le.mp hv),hq.1 _ (not_le.mp hv)]
     exact Flume.Script.home (sootS (hp.2 i)) (sootS (hq.2 i)) (hx i) (hy i) epochX (tendsto_add_atTop_nat 1) (Eventually.of_forall fun n x=> Grid.coinsP _ _ _ _ _ (fun r=> he ..) hv)
end YM.OPE.Cascade.Paver
