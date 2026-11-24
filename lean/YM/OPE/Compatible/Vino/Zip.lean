import YM.OPE.Compatible.Vino.Less
/-!
# full algebra. passage
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Float
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m:ℕ}
variable {K:Sponsor G}{T:Seasons K}{v v' b:ℝ}
variable (P:Flight i j)(A:Alps K T i v)(U:Alps K T j v') (B:Medal P.patch G K.K i)(R:ChartRatio G)
abbrev boxF (P:Flight i j)(K:Sponsor G)(h:Mag i j)(B:Medal P.patch G K.K i)(v:Train i): Boxes G P.patch K.K:=⟨i,h.1,B,v⟩
-- Cola path using true L
variable (h:Mag i j)(hp:A.gear=P.wing)(hz:U.gear=P.land)(hs:G.Simple)(b:ℝ)
local notation "Ψ"=> boxF P K h B A.gear
include h hp hz hs
lemma Fonter (n:Side) :∃ Z:Cola P.patch K.K Ψ A n b, ∀ i:ℕ, Z.light i= installed (subStud P.patch K.K (Z.jet i)).ratio (P.duo K.K.penalty).A0:=by
     let N:= 100 * Pressure.macroR P.patch+2; let M(i:ℕ):Side:= ⟨n.val*(i+N+1),mul_pos n.pos (by omega)⟩; have hv(i):N+1 ≤ (M i).val:=by apply le_trans (show N+1≤ i+N+1 by omega) (Nat.le_mul_of_pos_left _ n.pos)
     let S(i:ℕ):= P.visit (f:= (M i)*P.L) (c:=M i) K.K rfl
     have hh(i:ℕ): Bid.Larger (G:=G) (S i):=by
          have hm:= hv i; unfold N at hm; refine ⟨K.affordable P.patch,?_,?_⟩; change _ ≤ (M i).val*P.L.val; apply (le_trans _ (Nat.le_mul_of_pos_right (M i).val P.L.pos)); change 100* Pressure.macroR P.patch ≤ _; omega
          omega --
     choose g hG using fun i:ℕ=> testimony P K T A U hp hz h B (ha:=rfl) (hs:=hh i)
     let A'(i:ℕ):=installed (S i).ratio (P.duo K.K.penalty).A0; let t(i:ℕ):(S i).Choices:=Classical.arbitrary _
     let D:Cola P.patch K.K Ψ A n b:=⟨M,tendsto_atTop_mono (fun i=>(show i ≤ i+ N+1 by omega).trans (Nat.le_mul_of_pos_left _ n.pos)) tendsto_id,fun i=> dvd_mul_right ..,A',t,g,fun i=> (hG i).1,fun i=> Classical.choice (enrol (S i) P.odd Ψ (t i) (hG i).1 b hs)⟩
     exact ⟨D, fun i=> rfl⟩
omit h hp hz hs in
lemma Flair_price {X:Type} {g:Filter X}(p:X→ Seat d m (Shade G))(q: Seat d m (Shade G))(hq:Tendsto p g (𝓝 q))(x: deck (Shade G) n): Tendsto (fun t=>Flair (lilies m d _ (p t)) d x 0) g (𝓝 (Flair (lilies m d _ q) d x 0)):=by
      unfold Flair; refine tendsto_finsetSum _ ?_; intro i _; let y:Fin i→deck (Shade G) n:= fun _=>x; let M:=reading m i (0:Site n) (I:=Shade G) ∘L moduleAt m d i (Shade G); have he(q:Seat d m (Shade G)): Script.value 0 (lilies m d _ q i) x = M q y:= (instruments _ (sootS ((sproutV _ _ q).2 i)) 0 y).tsum_eq.trans (by rw [ContinuousLinearMap.comp_apply,toScript]; rfl); simp_rw [he]; exact ((show Continuous (fun x=> M x y) from (ContinuousMultilinearMap.apply ℝ _ _ y).continuous.comp M.continuous).tendsto _).comp hq
lemma invest (ht:LocalRatio R)(x:Phase)(d m:ℕ)(hm:45 ≤ m+1)(V:Seat (d+x.val) (m+1) (Shade G))(hx:V∈bed G (d+x.val) (m+1)) (hQ:Era Ψ A):
     sectorOp P.patch K.K A Ψ R b hm d x x hs hQ ht (warmEat (m:=m+1) V (atlasF G A.gear h.1 K.K))=
     warmEat (m:=m+1) (wagon P h.2.1 K.K G _ _ V) (atlasF G P.land h.2.1 K.K) :=by
         let D:= d+x.val; let y:= wagon P h.2.1 K.K G D (m+1) V
         let I:= sectorOp P.patch K.K A Ψ R b hm d x x hs hQ ht; let T:=lilies (m+1) (d+x.val) (Shade G)
         let V0:= warmEat (m:=m+1) V (atlasF _ A.gear h.1 K.K); let V1:= warmEat (m:=m+1) y (atlasF _ P.land h.2.1 K.K)
         have hh:V1∈ bed G D (m+1):=lockS K.K _ h.2.1 _ (bedW P h.2.1 K.K V hx (K.affordable _))
         apply lilies_inj (Shade G) D (m+1); refine scoreF (T (I V0)) (T V1) (sproutV _ _ _) (sproutV _ _ _) (fun i=>?_) (fun i=> (merit hh i).2.1) ?_
         · erw [publicity _ _ _ _ _ b _ _ _ _ _ _ _ V0];exact stir _
         intro n u; obtain ⟨Z,hZ⟩:= Fonter P A U B h hp hz hs b n; let p(i):= Z.jet i; let f (i):= p i * P.L
         let v(i):=warmEat (m:=m+1) V (pointAt _ A.gear h.1 K.K (f i)); let r(i):= warmEat (m:=m+1) y (pointAt _ P.land h.2.1 K.K (p i)); let l:Filter ℕ:=atTop
         have hF:Tendsto (fun i=>(f i).val) l atTop := tendsto_atTop_mono (fun i=>Nat.le_mul_of_pos_right (p i).val P.L.pos) Z.tip
         have he:Tendsto v atTop (𝓝 V0):= fixStrong (loreLap (m:=m+1) (farN _ f _ _ _ hF)) _ _ (tendsto_const_nhds (x:=V)); have hL:Tendsto r atTop (𝓝 V1):= fixStrong (loreLap (m:=m+1) (farN _ p _ _ _ Z.tip)) _ _ (tendsto_const_nhds (x:=y))
         -- col limits exact
         let u':=(spool G n).symm u
         obtain ⟨W,hW,w⟩:= liquidity P.patch K.K Ψ A R hs ht hm (d:=d) b
         obtain ⟨z,hz,H⟩:= bootPrice (Shade G) (m+1) D (-(1/2:ℝ)) (atlasF G A.gear h.1 K.K).positive
         have hg(i):‖v i‖≤ z*‖V‖:= H (pointAt G A.gear h.1 K.K (f i)) le_rfl _
         have ha(i):Tide (impulse x (T (v i))) d (m+1) (z*‖V‖):= nip x _ _ _ _ (Volume.raise _ (sproutV (m+1) D (v i)) le_rfl (hg i))
         let q(i):= impulse x (T (v i)); let g(i:ℕ):= Flair (T (I (v i))) D u (0:Site n); let r' (i:ℕ):= Flair (T (r i)) D u (0:Site n)
         have hk(i): g i=(inkM (sculpt P.patch K.K Ψ A R b (q i) d) d 0 u').seq x.val:=by unfold g; rw [vein_i, show spool G n u'=u from (spool G n).apply_symm_apply _,show T (I (v i))= _ from publicity _ _ _ _ _ b _ _ _ hm d x x (v i)]; rfl
         have hm'(i): r' i= Z.atW R 0 u' i d x (q i):=by
              unfold Cola.atW; let S:= P.visit (c:=p i) (f:=f i) K.K rfl; let L:= Z.accord i; rw [hZ i] at L
              let v':=Booklet (Z.yarn i) G u'; let z':= wrap (p i) (lift (0:Site n)); have hb:= fealty P h (c:=p i) (f:=f i) rfl x d m V hx A R ht B hp b z' v' (Z.paths i) (Z.stems i) L (Z.traceX i)
              -- Flair reindex Booklet
              have hc: r' i= Flair (T (r i)) D (spool G (p i) v') z':=by
                   let a:= impulse x (T (r i)); have ht:= labRel (Z.yarn i) z' u' d a; have hx: trimT _ _ (Z.yarn i) z'=0:=(lease _ _).trans (wrap_lift _); rw [hx] at ht; have he:= congr_arg (fun v:Token=>v.seq x.val) ht ; erw [vein_i,vein_i, show spool G n u'=u from (spool G n).apply_symm_apply _, show a x=T (r i) from Pi.single_eq_same x _] at he; exact he.symm
              exact hc.trans hb.symm
         -- uniqueness
         have htV:Tendsto (fun i=> r' i-g i) l (𝓝 0):=by simp_rw [hk, hm']; exact Z.margin _ _ _ _ _ _ _ _ w hW (by positivity) ha
         have hp':= Flair_price (fun i=> I (v i)) _ ((I.continuous.tendsto V0).comp he) u; have hy:= (Flair_price r _ hL u).sub hp'; exact (sub_eq_zero.mp (tendsto_nhds_unique hy htV)).symm
end YM.OPE.Silt.Float
