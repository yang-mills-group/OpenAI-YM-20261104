import YM.OPE.Compatible.Vino.Mello
/-!
# Turn linear bunch
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
variable {α β:ℝ} {p q:Muse G}
def Rainbow (p:Muse G):Prop:=∀ i j,sorted (p i j)
lemma bright (hp:Rainbow p)(hq:Rainbow q): Rainbow (p+q):=fun i j k=>by rw [Pi.add_apply,Pi.add_apply]; change swing k (p i j)+swing k (q i j)= _; rw [hp i j k,hq i j k]
lemma brighter (s:ℝ)(hp:Rainbow p):Rainbow (s • p):=fun i j k=>by rw [Pi.smul_apply, Pi.smul_apply]; change s • swing k (p i j) = _; rw [hp i j k]
lemma tidal (hp:Tide p d m α)(hq:Tide q d m β): Tide (p+q) d m (α+β):=fun i=>Volume.add _ (hp i) (hq i)
lemma tidalS (hp:Tide p d m α)(x:ℝ): Tide (x • p) d m (‖x‖*α):=fun i=>Volume.spread _ x (hp i)
lemma MsUnique (hp:Tide p d m α)(hq:Tide q d m β)(h:Rainbow p)(g:Rainbow q)(he:∀ n:Side,∀ x:Bid.Dir G n, inkM p d 0 x= inkM q d 0 x):p=q:=by
    funext i; apply scoreF _ _ (hp i) (hq i) (h i) (g i); intro n u; specialize he n ((spool G n).symm u); apply Eq.trans (a:=Flair (p i) (d+i.val) u _) (b:=(inkM p d (0:Site n) ((spool G n).symm u)).seq i.val); rw [vein_i, ContinuousLinearEquiv.apply_symm_apply]; rw [he,vein_i,ContinuousLinearEquiv.apply_symm_apply]
variable (P:Patch)(C:KernelChoices) (U:Boxes G P C) (A:Alps K T i v) (V:ChartRatio G)
variable (b:ℝ)(h:Era U A)(hs:G.Simple)(ht:LocalRatio V)(hm:45≤m)
local notation "ΠX" p:arg => sculpt P C U A V b p d
lemma rainbow (v:Muse G)(b:ℝ): Rainbow (sculpt P C U A V b v d):= fun _ _=> stir _
include hs ht hm h
lemma levy (hx:Tide p d m α)(hq:Tide q d m β): ΠX (p+q) = ΠX p + ΠX q:=by
     obtain ⟨D,hD,H⟩:= liquidity P C U A V hs ht (show 1+44 ≤ m from hm) (d:=d) b; let Y:= sculpt P C U A V b
     have hK:= tidal hx hq; let ha:= established P C U A V b hs H h p α hx; let hv:=established P C U A V b hs H h q β hq; refine MsUnique (established P C U A V b hs H h _ _ hK) (tidal ha hv) (rainbow _ _ _ _ _ _ _) (bright (rainbow _ _ _ _ _ _ _) (rainbow _ _ _ _ _ _ _)) fun n x=>?_ ; obtain ⟨X⟩:=mach P C U A b h hs n; let f(u:Muse G)(i:Phase)(k:ℕ):=X.atW V 0 x k d i u; have he(i:Phase):f (p+q) i=f p i+f q i:=by
          funext k; unfold f Cola.atW; erw [jetSum A V (subStud P C (X.jet k)) P.odd_side (X.stems k) U _ _ _ (X.traceX k) _ _ _ _ hx hq ht]; fin_cases i<;>rfl
     rw [Ink_sum 0 _ _ _ d _ _ ha hv]; have hh (i:Phase): (inkM (ΠX (p+q)) d 0 x).seq i.val=(inkM (ΠX p) d 0 x).seq i.val+(inkM (ΠX q) d 0 x).seq i.val:=by
         apply tendsto_nhds_unique (X.earns _ x 0 i hs ht hm _ _ hK); rw [show (fun k=>_)= _ from he i]; exact (X.earns _ _ _ _ hs ht hm _ _ hx).add (X.earns _ _ _ _ hs ht hm _ _ hq)
     exact JetS.eta _ _ (hh 0) (hh 1) (hh 2)
lemma levee (r:ℝ)(hx:Tide p d m α): ΠX (r • p) = r • (ΠX p):=by
     obtain ⟨D,hD,H⟩:= liquidity P C U A V hs ht (show 1+44 ≤ m from hm) (d:=d) b; have htX:=tidalS hx r; let he:=established P C U A V b hs H h p _ hx
     refine MsUnique (established P C U A V b hs H h _ _ htX) (tidalS he r) (rainbow _ _ _ _ _ _ _) (brighter r (rainbow _ _ _ _ _ _ _)) fun n x=>?_ ; obtain ⟨X⟩:= mach P C U A b h hs n
     let f(u:Muse G)(i:Phase)(k:ℕ):= X.atW V 0 x k d i u; have ha(i:Phase): f (r • p) i=r • f p i:=by
          funext k; unfold f Cola.atW; erw [jetL A V (subStud P C (X.jet k)) P.odd_side (X.stems k) U _ _ _ (X.traceX k) _ _ _ hx ht]; fin_cases i<;> simp [JetS.seq, JetS.plainJ]
     have hh(i:Phase): (inkM (ΠX (r • p)) d 0 x).seq i.val=r * (inkM (ΠX p) d 0 x).seq i.val:=by
          apply tendsto_nhds_unique (X.earns _ _ _ _ hs ht hm _ _ htX); rw [show (fun k=>_)= _ from ha i]; exact (X.earns _ _ _ _ hs ht hm _ _ hx).const_mul r
     rw [Ink_scale]; apply JetS.eta; exact hh 0; change _= r*_+ (0:ℝ)*_; rw [zero_mul,add_zero]; exact hh 1; change _=r*_+(0:ℝ)*_+(0:ℝ)*_; rw [zero_mul,zero_mul,add_zero,add_zero]; exact hh 2
end YM.OPE.Cascade.Paver
