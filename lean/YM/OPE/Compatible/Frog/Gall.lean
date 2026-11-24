import YM.OPE.Compatible.Frog.Froth
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
open Arc
local notation "Lf" => Tested.germ
lemma landP {V E: Type}[Fintype E]{y x:ℝ→ Libra.Keys G E}{s:ℝ→ Libra.Tile G V}{R: Score E V}{p: ScriptJ (Libra.Keys G E)}{u v: Libra.Keys G E}(h:R.Marbles p)(hp:R.Track x y s) (hx: Tendsto (fun t:ℝ=> t⁻¹ • x t) Lf (𝓝 u))(hy: Tendsto (fun t:ℝ=> t⁻¹ • y t) Lf (𝓝 v))(l:Phase)(h0:∀ i<l,∀ x,(p x).seq i.val=0): (p u).seq l.val=(p v).seq l.val:=by
      let g(t:ℝ):= t⁻¹ • x t; let f(t:ℝ):= t⁻¹ • y t; have hg:Gael g:=Gael.walk x hp.hX hp.gx; have hf:Gael f:=Gael.walk y hp.hY hp.gy; have he:mine (p∘g)= mine (p∘f):=(OPE.Drift.pores R h.toll).1 h hp
      have hQ(w:ℝ→Libra.Keys G E)(q:Libra.Keys G E)(hg:Gael w)(hv:Tendsto w Lf (𝓝 q)):(mine (p∘w)).seq l.val=(p q).seq l.val:=by
           let T:=p ∘ w; let z(i:Phase)(t:ℝ):=(p (w t)).seq i.val; have hZ(i): Reads (z i) (trill (z i)):= Gael.oath (Gael.climb _ (h.toll i.val) hg); rw [Fitted.totals (p:=p∘w) (hZ 0) (hZ 1) (hZ 2)]; have ht(i:Phase): (p q).seq i.val=(trill (z i)).s:= tendsto_nhds_unique (((h.toll i).smooth.continuous.tendsto q).comp hv) (hZ i).limit
           rw [ht]; have hW(i:Phase)(hi:i < l):trill (z i)=0:=Gael.chooses ((Reads.constants (0:ℝ)).cong (Eventually.of_forall fun i'=> h0 i hi _)); fin_cases l
           · simp [assembleJ,ski,JetS.seq]
           · rw [hW 0 (by decide)]; simp [assembleJ,ski,JetS.seq]
           rw [hW 0 (by decide),hW 1 (by decide)];simp [assembleJ,ski,JetS.seq]
      rw [← hQ _ _ hg hx, he, hQ _ _ hf hy]
lemma yachts (n:Side)(z:Site n)(d:ℕ)(Q:Muse G)(l:Phase)(h:∀ i<l,Q i=0) (i:Phase)(hi:i<l)(x:Bid.Dir G n) : (inkM Q d z x).seq i.val=0:=by rw [Paver.vein_i,h i hi,flair0]
lemma cycleB (h:Pathic d Q)(l:Phase)(H:∀ i<l,Q i=0) (x:deck (Blend G) n)(z: Site n): Flair (Q l) (d+l.val) (lac G n x) z= Flair (Q l) (d+l.val) (lac G n (fderiv ℝ (fog G n) 0 x)) z:=by
     let y(t:ℝ):= t • x; have he :ContDiffAt ℝ ∞ y 0:=contDiffAt_id.smul contDiffAt_const; let z':= solidY G n; let u (t:ℝ):= z' (y t); let Z:= fog G n; let v(t:ℝ):=z' (Z (y t)); let s (t:ℝ):= plover G (y t)
     obtain ⟨hf,hx⟩:= fogDial G n; have hz: y 0=0:= zero_smul ..
     have hT:(tor n).Track u v s:=by
          refine ⟨z'.contDiff.contDiffAt.comp _ he,z'.contDiff.contDiffAt.comp _ ((hz.symm ▸ (hx.of_le le_top) : ContDiffAt ℝ ∞ Z (y 0)).comp 0 he),by unfold u; rw [hz,map_zero],by unfold v; rw [hz,show Z 0=0 from hf,map_zero],?_,?_⟩
          · exact ((show Tendsto y (𝓝 0) (𝓝 0) from hz ▸ he.continuousAt).eventually (fog_gr G n)).mono fun i hi=> (Mar_ord (u i) (v i) (s i)).2 hi.symm
          intro i; unfold s plover; exact (G.exp_jet.of_le le_top).contDiffAt.comp 0 ((((ups G 0) ∘L lookS (stave G) i).contDiff.contDiffAt.comp _ he).neg)
     have hU: Tendsto (fun t:ℝ=> t⁻¹ • u t) Lf (𝓝 (z' x)):=by unfold u; simp_rw [← map_smul]; exact (z'.continuous.tendsto _).comp (slopeX x)
     have hv: Tendsto (fun t:ℝ=> t⁻¹ • v t) Lf (𝓝 (z' (fderiv ℝ Z 0 x))):=by unfold v; simp_rw [← z'.map_smul]; exact (z'.continuous.tendsto _).comp (slopeZ x (hx.of_le le_top) hf)
     have ha (q:deck (Blend G) n): ((inkM Q d z) (z' q)).seq l.val= Flair (Q l) (d+l.val) (lac G n q) z:=by rw [Paver.vein_i]; change Flair _ (d+l.val) ((spool G n) ((spool G n).symm (lac G n q))) _=_; rw [ContinuousLinearEquiv.apply_symm_apply]
     rw [←ha,←ha]; exact landP (h n z) hT hU hv l (yachts n z d Q l H)
lemma cycleBG (h:Pathic d Q)(l:Phase)(H:∀ i<l,Q i=0)(u:deck (Shade G) n)(v:deck G.ColorIndex n)(z:Site n): Flair (Q l) (d+l.val) (u+cliff v) z= Flair (Q l) (d+l.val) u z:=by
      let x:deck (Blend G) n:=fun i=> Sum.elim (fun j=>u (i.1,j)) (fun j=>v (i.1,j)) i.2; rw [show u+cliff v=lac G n (fderiv ℝ (fog G n) 0 x) by ext1 i; change u _+(v _-v _)=_; rw [fogStem]; change _=u _+v _-v _; ring, ← cycleB h l H x]; rfl
lemma cycleBHue (h:Pathic d Q)(l:Phase)(H:∀ i<l,Q i=0)(u:deck (Shade G) n)(p:G.El)(z:Site n): Flair (Q l) (d+l.val) (hue p u) z=Flair (Q l) (d+l.val) u z:=by
       let T:= spool G n; let b:=T.symm u; let c:= T.symm (hue p u); let s (t:ℝ)(i: Site n):G.El:= p; let x:= fun t:ℝ=> t• b; let y:= fun t:ℝ=> t• c
       have hv:(tor n).Track x y s:=by
            refine ⟨contDiffAt_id.smul contDiffAt_const,contDiffAt_id.smul contDiffAt_const, zero_smul ..,zero_smul ..,Eventually.of_forall (fun t=>?_),fun _=> by unfold s; exact contDiffAt_const⟩; funext i; change p * G.lieExp (t • b i) * p⁻¹= G.lieExp (t • c i)
            have he: c i=G.adjoint p (b i):=rfl; rw [he,← map_smul]; apply G.mat_injective; rw [G.mat_lieExp,G.mat_adjoint,G.exp_conjugate,G.mat_mul,G.mat_mul,G.mat_lieExp]; rfl
       rw [← show T b=u from T.apply_symm_apply _,show hue p (T b)=T c from by rw [show T b=u from T.apply_symm_apply _,show T c=hue p u from T.apply_symm_apply _]]
       rw [← show _= Flair (Q l) (d+l.val) (T b) z from Paver.vein_i Q d z b l, ← show _=Flair (Q l) (d+l.val) (T c) z from Paver.vein_i Q d z c l]; exact (landP (h n z) hv (slopeX b) (slopeX c) l (yachts n z d Q l H)).symm
lemma walkL (h:Pathic d Q)(l:Phase)(H:∀ i<l,Q i=0)(hq:Summable (Q l k))(he:k ≤ d+l.val)(hp:sorted (Q l k)): abides (Q l k)∧ painted (Q l k):=by
     constructor
     · intro i n w s; let U:=deck (Shade G) n; let V:= deck G.ColorIndex n; let X:= cliffL G n; let f:=ContinuousLinearMap.fst ℝ U V; let g:=ContinuousLinearMap.snd ℝ U V; let t:=Q l k
       have hX(z:U × V) : Script.value 0 t ((f+X ∘L g) z)= Script.value 0 t (f z):=by
            apply coinsP _ _ _ _ (d:=d+l.val) _ _ he; intro c; rw [_root_.add_apply,smul_add,ContinuousLinearMap.comp_apply,← X.map_smul]; exact cycleBG h l H _ _ _
       let v:Fin k→ U × V:=update (fun j=> (w j,(0:V))) i (0,s); have hz:=dwell (f+X ∘L g) f (Q l) k 0 hq hp hX v; let T:= orchestra t (0:Site n); have hF(i:Fin k→ deck (Shade G) n): scribe 0 t i=T i:= (instruments t hq ..).tsum_eq; have hh: (f+X ∘L g)∘ v= update w i (cliff s):=by funext a; unfold Function.comp v; by_cases he:a=i; subst a; simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,update_self]; change 0+X s= _; rw [zero_add];rfl; rw [update_of_ne he,update_of_ne he]; change w _+X 0=_; rw [map_zero, add_zero]
       rw [← hh,hz]; exact (hF _).trans (T.map_coord_zero i (show f (v i)=0 by rw [show v i=_ from update_self i _ _]; rfl))
     intro n u p; let A:= hueL p n; let I:=ContinuousLinearMap.id ℝ (deck (Shade G) n); exact dwell A I _ _ _ hq hp (fun x=> coinsP _ _ _ _ _ (fun v=> by rw [← A.map_smul]; exact cycleBHue h l H (v • x) p _) he) u
end YM.OPE.Cascade.Grid
