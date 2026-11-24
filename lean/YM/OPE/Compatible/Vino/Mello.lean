import YM.OPE.Compatible.Vino.Jip
/-!
# ascend from arbitrary size. Dequant
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
-- chooseon large cofinal sh
structure Cola (P:Patch)(C:KernelChoices)(U:Boxes G P C) (A:Alps K T i v)(n:Side)(b:ℝ) where
      jet : ℕ→ Side
      tip : Tendsto (fun i=>(jet i).val) atTop atTop
      yarn (k:ℕ): n.val∣(jet k).val
      light (k:ℕ) : Matrix (Body 1 (jet k*P.L)) (Body 1 (jet k)) ℝ
      stems (k:ℕ): (subStud P C (jet k)).Choices
      paths (k:ℕ): Bid.Dir G (jet k) → AxisChart G (forest (subStud P C (jet k)).ratio P.odd_side)
      accord (k:ℕ): licensed (subStud P C (jet k)) P.odd_side U A.clip A.live (light k) A.sky (paths k)
      traceX (k:ℕ): FibreRep (subStud P C (jet k)) P.odd_side U (stems k) A (paths k) b
lemma mach (b:ℝ)(X: Era U A)(hs:G.Simple) (n:Side): Nonempty (Cola P C U A n b):=by
       obtain ⟨t,ht⟩:=X; let M (i:ℕ): Side:=⟨n.val*(i+t+1),mul_pos n.pos (by omega)⟩; have hz(i):i+t+1≤(M i).val:= Nat.le_mul_of_pos_left _ n.pos; choose L F h using fun i:ℕ=> ht (M i) (le_trans (show t≤ i+t+1 by omega) (hz i)); let y(i):(subStud P C (M i)).Choices:= Classical.arbitrary _
       exact ⟨⟨M,tendsto_atTop_mono (fun i=> (show i≤ i+t+1 by omega).trans (hz i)) tendsto_id,fun i=>dvd_mul_right ..,L,y,F,h,fun i=> Classical.choice (enrol (subStud P C (M i)) P.odd_side _ (y i) (h i) _ hs)⟩⟩
namespace Cola
variable {P C U A} (X:Cola P C U A n b)
local notation "S(" i ")"=> subStud P C (X.jet i)
-- evaluate at v periodic
abbrev atW (p: Site n)(u:Bid.Dir G n)(k:ℕ)(d:ℕ)(i:Phase)(q:Muse G):ℝ:= (TracePay S(k) P.odd_side U A (X.stems k) (X.paths k) V d q b (wrap (X.jet k) (lift p)) (X.traceX k) (Booklet (X.yarn k) G u)).seq i.val
theorem margin (u:Bid.Dir G n)(p:Site n)(i:Phase)(d:ℕ)(m:ℕ)(w z:ℝ)(hp:Paid P C U A V m 1 d w b)(h:0≤w)(hz:0≤z){q:ℕ→ Muse G}(hT:∀ i,Tide (q i) d m z): Tendsto (fun k:ℕ=> X.atW V p u k d i (q k) - (inkM (sculpt P C U A V b (q k) d) d p u).seq i.val) atTop (𝓝 0):=by
      let c:=w*z*(1+‖spool G n u‖)^glideZ d
      have hg: Tendsto (fun i=>(X.jet i).val) atTop atTop:= X.tip
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      apply squeeze_zero (g:=fun i=> c/ (X.jet i).val) (fun _=>norm_nonneg _) _ (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hg)); intro k
      rw [le_div_iff₀ (by exact_mod_cast (X.jet k).pos),mul_comm]; let P':=wrap (X.jet k) (lift p); have ht:= hp (X.jet k) (X.light k) (X.paths k) (X.accord k) (X.stems k) (X.traceX k) P' (q k) z (hT k); let v:=Booklet (X.yarn k) G u
      have hb: trimT (X.jet k) n (X.yarn k) P'=p:=(lease (X.yarn k) _).trans (wrap_lift p); have hv:=ht.2 v i; unfold Mold Shell.grain at hv; rw [pow_one, show inkM _ _ _ v= _ from labRel (X.yarn k) P' u d (sculpt P C U A V b (q k) d),hb] at hv; exact hv.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (add_le_add_right (book_eq (X.yarn k) u) _) _) (by positivity))
lemma earns (u:Bid.Dir G n)(p:Site n)(i:Phase)(hs:G.Simple)(hv:LocalRatio V)(hm:45 ≤ m)(q:Muse G)(w:ℝ)(h:Tide q d m w): Tendsto (fun k=>X.atW V p u k d i q) atTop (𝓝 ((inkM (sculpt P C U A V b q d) d p u).seq i.val)):=by
     obtain ⟨A,hA,H⟩:= liquidity P C U A V hs hv (show 1+44≤m from hm) (d:=d) b; let q' (_:ℕ):=q; exact tendsto_sub_nhds_zero_iff.mp (margin V X u p i d m _ _ H hA (Sack.coins ((h 0).2 0)) (q:=q') (fun _=>h))
end Cola
end YM.OPE.Cascade.Paver
