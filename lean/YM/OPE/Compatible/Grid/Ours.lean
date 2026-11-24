import YM.OPE.Compatible.Grafts.Spat
import YM.OPE.Compatible.Aroma.Clasp
import YM.OPE.Compatible.Seeds.Pump
/-! # Lowest coupling and grade maps -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Grid
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series ScriptJ GaussianScore Work.F05 Rill Glass Coin Pilot Radial Flock
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier
variable {I J:Type}{G:Gauge}{n c f:Side}{d j k m:ℕ}{Q:Muse G}
local notation "Lf" => Tested.germ
-- leading leg read through true t expansion
lemma ribFocus {V E: Type}[Fintype E]{y x:ℝ→ Libra.Keys G E}{s:ℝ→ Libra.Tile G V}{R: Score E V}{p: ScriptJ (Libra.Keys G E)}{u v: Libra.Keys G E}(h:R.Marbles p)(hp:R.Track x y s) (hx: Tendsto (fun t:ℝ=> t⁻¹ • x t) Lf (𝓝 u))(hy: Tendsto (fun t:ℝ=> t⁻¹ • y t) Lf (𝓝 v)): (p u).s=(p v).s:=by
     have ht:Tendsto (fun t:ℝ=> t) Lf (𝓝 0):= nhdsWithin_le_nhds |> tendsto_id.mono_left
     let T:= Libra.Keys G E
     have H(r:ℝ→T)(x:T)(hr:Tendsto r Lf (𝓝 x)): Tendsto (fun t:ℝ=> (p (r t)).atK t) Lf (𝓝 (p x).s):=by
          let f (i:ℕ)(y:T):ℝ:=(p y).seq i; have he (i:Phase): Tendsto (fun t:ℝ=> f i.val (r t)) Lf (𝓝 (f i.val x)):= ((h.toll i).smooth.continuous.tendsto x).comp hr
          have hh := ((he 0).add (ht.smul (he 1))).add ((ht.pow 2).smul (he 2))
          convert! hh using 2; simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,zero_smul,add_zero]
          rfl
     exact sub_eq_zero.mp (tendsto_nhds_unique ((H _ _ hx).sub (H _ _ hy)) ((h.honors hp).trans_tendsto (by simpa only [zero_pow (show 3≠0 by norm_num)] using ht.pow 3)))
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
lemma slopeZ {r:E→F}(u:E)(h:ContDiffAt ℝ ∞ r 0)(hg:r 0=0): Tendsto (fun t:ℝ=> t⁻¹ • r (t • u)) Lf (𝓝 (fderiv ℝ r 0 u)) := by
       have ht:= ((h.differentiableAt (by simp)).hasFDerivAt.hasLineDerivAt u).tendsto_slope_zero; simp only [zero_add,hg,sub_zero] at ht; exact ht.mono_left (nhdsWithin_mono _ (by simp))
lemma slopeX (u:E): Tendsto (fun t:ℝ => t⁻¹ • (t • u)) Lf (𝓝 u):= by
       apply tendsto_const_nhds.congr'; filter_upwards [Tested.eventually_pos] with i hi; rw [inv_smul_smul₀ hi.ne']
lemma cog (h:Pathic d Q) (x:deck (Blend G) n)(z: Site n): Flair (Q 0) d (lac G n x) z= Flair (Q 0) d (lac G n (fderiv ℝ (fog G n) 0 x)) z:=by
     let y(t:ℝ):= t • x; have he :ContDiffAt ℝ ∞ y 0:=contDiffAt_id.smul contDiffAt_const; let z':= solidY G n; let u (t:ℝ):= z' (y t); let Z:= fog G n; let v(t:ℝ):=z' (Z (y t)); let s (t:ℝ):= plover G (y t)
     obtain ⟨hf,hx⟩:= fogDial G n; have hz: y 0=0:= zero_smul ..
     have hT:(tor n).Track u v s:=by
          refine ⟨z'.contDiff.contDiffAt.comp _ he,z'.contDiff.contDiffAt.comp _ ((hz.symm ▸ (hx.of_le le_top) : ContDiffAt ℝ ∞ Z (y 0)).comp 0 he),by unfold u; rw [hz,map_zero],by unfold v; rw [hz,show Z 0=0 from hf,map_zero],?_,?_⟩
          · exact ((show Tendsto y (𝓝 0) (𝓝 0) from hz ▸ he.continuousAt).eventually (fog_gr G n)).mono fun i hi=> (Mar_ord (u i) (v i) (s i)).2 hi.symm
          intro i; unfold s plover; exact (G.exp_jet.of_le le_top).contDiffAt.comp 0 ((((ups G 0) ∘L lookS (stave G) i).contDiff.contDiffAt.comp _ he).neg)
     have hU: Tendsto (fun t:ℝ=> t⁻¹ • u t) Lf (𝓝 (z' x)):=by unfold u; simp_rw [← map_smul]; exact (z'.continuous.tendsto _).comp (slopeX x)
     have hv: Tendsto (fun t:ℝ=> t⁻¹ • v t) Lf (𝓝 (z' (fderiv ℝ Z 0 x))):=by unfold v; simp_rw [← z'.map_smul]; exact (z'.continuous.tendsto _).comp (slopeZ x (hx.of_le le_top) hf)
     have ha (q:deck (Blend G) n): ((inkM Q d z) (z' q)).s= Flair (Q 0) d (lac G n q) z:=by change Flair _ (d+0) ((spool G n) ((spool G n).symm (lac G n q))) _=_; rw [add_zero,ContinuousLinearEquiv.apply_symm_apply]
     rw [←ha,←ha]; exact ribFocus (h n z) hT hU hv
lemma cogG (h:Pathic d Q)(u:deck (Shade G) n)(v:deck G.ColorIndex n)(z:Site n): Flair (Q 0) d (u+cliff v) z= Flair (Q 0) d u z:=by
      let x:deck (Blend G) n:=fun i=> Sum.elim (fun j=>u (i.1,j)) (fun j=>v (i.1,j)) i.2; rw [show u+cliff v=lac G n (fderiv ℝ (fog G n) 0 x) by ext1 i; change u _+(v _-v _)=_; rw [fogStem]; change _=u _+v _-v _; ring, ← cog h x]; rfl
lemma cogHue (h:Pathic d Q)(u:deck (Shade G) n)(p:G.El)(z:Site n): Flair (Q 0) d (hue p u) z=Flair (Q 0) d u z:=by
       let T:= spool G n; let b:=T.symm u; let c:= T.symm (hue p u); let s (t:ℝ)(i: Site n):G.El:= p; let x:= fun t:ℝ=> t• b; let y:= fun t:ℝ=> t• c
       have hv:(tor n).Track x y s:=by
            refine ⟨contDiffAt_id.smul contDiffAt_const,contDiffAt_id.smul contDiffAt_const, zero_smul ..,zero_smul ..,Eventually.of_forall (fun t=>?_),fun _=> by unfold s; exact contDiffAt_const⟩; funext i; change p * G.lieExp (t • b i) * p⁻¹= G.lieExp (t • c i)
            have he: c i=G.adjoint p (b i):=rfl; rw [he,← map_smul]; apply G.mat_injective; rw [G.mat_lieExp,G.mat_adjoint,G.exp_conjugate,G.mat_mul,G.mat_mul,G.mat_lieExp]; rfl
       rw [← show T b=u from T.apply_symm_apply _,show hue p (T b)=T c from by rw [show T b=u from T.apply_symm_apply _,show T c=hue p u from T.apply_symm_apply _]]
       exact (ribFocus (h n z) hv (slopeX b) (slopeX c)).symm
end YM.OPE.Cascade.Grid
