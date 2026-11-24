import YM.OPE.Compatible.Estuary.Saga
/-!
# Tape WARD lower-income estimate
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Votive Tree
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n c f L:Side}{P:Patch}{K:KernelChoices}{I J:Type}{m k r d:ℕ}{σ C z:ℝ}
namespace Script
open Page Virgin Planned.PrimaryIntegral295.Carrier
-- Pack exists uniform sponsor.
lemma stakeFog (G:Gauge)(n m:ℕ)(hn:0<n):∃ z:ℝ,0 ≤ z∧∀ (q:(r:ℕ)→Script (Shade G) r) (Q:ℝ) (Y:∀ n:Side,Config G n→ℝ),0 ≤ Q→(∀ r,0<r→ r<n→ soot m (q r) Q) → (∀ i,ContDiffAt ℝ ω (Y i ∘ represent) 0 ∧ (∀ r,r≤n→Voice (q r) (spool G i).toContinuousLinearMap (Y i∘represent))∧∀ U f,Y i (Lattice.gauge f U)=Y i U)→ ∃ p: Script (Blend G) n, soot m p (z*Q)∧∀ (c:Side)(x:deck (Blend G) c),narrate c (q n) (lac G c x)=narrate c (q n) (lac G c (fderiv ℝ (fog G c) 0 x))+narrate c p x:=by
    obtain ⟨D,hd,H⟩:=trounce (stave G) (vigil G) (fun i=>(vigilA G i).2) (fun i=>(vigilA G i).1) m n hn
    choose c hc Hc using faneFund G m; let C:=∑ i:Fin (n+1), c i; have hC:0 ≤ C:= Finset.sum_nonneg fun i _=> hc _
    refine ⟨D*C,mul_nonneg hd hC,fun q z Y hz hp hh=>?_⟩
    let Q(k):=raft (fane G) (q k); have hk (i:ℕ) (ha: 0 < i)(ht: i < n): soot m (Q i) (C*z):= by
       let j: Fin (n+1):=⟨i,by omega⟩; refine (Hc i (q i) z (hp i ha ht)).tips (mul_le_mul_of_nonneg_right ?_ hz); exact Finset.single_le_sum (f:=fun i:Fin (n+1)=> c i) (fun i _=>hc _) (mem_univ j)
    obtain ⟨p,he,hP⟩:= H Q (C*z) (mul_nonneg hC hz) hk; rw [mul_assoc]; refine ⟨p,he,fun i x=>?_⟩
    obtain ⟨hR,hT,hO⟩:= hh i; let A:= Y i ∘ represent; let u:=solidY G i; let v:=fog G i; let T:= A∘ u; have hu:ContDiffAt ℝ ω T 0:= ((u.map_zero.symm ▸ hR : ContDiffAt ℝ ω A (u 0))).comp _ u.contDiff.contDiffAt; have hw:= hP i T hu (fun r hv hn y=>flow_at (q r) hR (hT r hn.le) (sootS (hp r hv hn)) y) x
    have ht : T∘v=ᶠ[𝓝 0] T :=by
       filter_upwards [fog_gr G i] with x hx; change Y i _=Y i _; erw [hx];exact hO ..
    have hf (x:deck (Blend G) i): iteratedFDeriv ℝ n T 0 (fun _=> x)=narrate i (q n) (lac G i x):=by
       rw [show iteratedFDeriv ℝ n T 0= _ from jets_linear u (hR.of_le le_top)]; change iteratedFDeriv ℝ n (Y i∘ represent) 0 (fun _=>u x)=_; rw [← hT n le_rfl (fun _=> u x)]; apply congr_arg (library _ _); ext1 j; exact (spool G i).apply_symm_apply _
    rw [← hf,← hf]; exact ((congr_arg (fun f:Tensor.T _ ℝ n=>f fun _=>x) (ht.iteratedFDeriv ℝ n|>.eq_of_nhds)).symm.trans hw)
section slide
variable (Z:Boxes G P K) (A:Lines P.L) (hp:Whole A)
def player (q:Script (Shade G) r):=raft Z.main (payVolume (drip G P.L) q)
lemma player_bill (q:Script (Shade G) r)(hq:folk q):folk (player Z q):= folkT Z.rocket2 (fun i=> volume_bill _ (drip_cash ..) _ _ (hq i).choose_spec)
-- same for P.S generated
def Kine (x:Boxes G P K)(A:Lines P.L):Prop:= ∃ t:ℕ→ Side,Tendsto (fun i=> (t i).val) atTop atTop ∧∀ i,let S:StepData (t i) (t i*P.L):=⟨P,K,rfl⟩
                                         installed S.ratio (x.C.highCross x.g) = tensor G (extracted S (forest S.ratio P.odd_side) (installed S.ratio A))
include hp
lemma actor_slide (hq:Kine Z A){Q: Script (Shade G) (r+1)}(hg: Summable Q)(hX:Idem Q){p: Script (Blend G) (r+1)}(hS:Summable p) (hx:∀ c:Side,∀ x:deck (Blend G) c,narrate c Q (lac G c x)=narrate c Q (lac G c (fderiv ℝ (fog G c) 0 x))+narrate c p x):
   stitch (player Z Q)= payVolume (chrome G.ColorIndex A) Q -stitch (payVolume (kite G P A) p):=by
     have hi:Whole (kite G P A):=kite_ne P A hp; have hh:Whole (chrome G.ColorIndex A):= chrome_sum hp; let T:= payVolume (kite G P A) p; let Y:= player Z Q; let V:= payVolume (chrome G.ColorIndex A) Q; have ht: Summable Y:= VolAll _ (payact Z.main Z.rocket2) _ (VolAll _ (drip_cash ..) _ hg); have hh':Summable T:= VolAll _ hi p hS; have hm:Summable V:= VolAll _ hh Q hg
     have he{p:Script (Shade G) (r+1)}(hk:Summable p):Summable (stitch p):= sootS (silt_cost (adjusted (Tsumm hk)))
     have htQ:=he ht; have hY:=he hh'; have hM: Summable (V+(-1:ℝ)•stitch T):=hm.add (hY.const_smul (-1:ℝ)); change stitch Y=V-stitch T; rw [sub_eq_add_neg,show -stitch T=(-1:ℝ) • stitch T by simp]; obtain ⟨t,hm',H⟩:=hq
     refine away htQ hM (stampV Y ht) (idemAdd _ _ (tribal Q hg _ hh hX) (idemScale _ _ (stampV T hh')) hm (hY.const_smul (-1:ℝ))) t hm' (Eventually.of_forall fun i x=>?_)
     let S:StepData (t i) (t i*P.L):=⟨P,K,rfl⟩; obtain ⟨v,rfl⟩:= (spool G (t i)).surjective x; obtain ⟨ha,hL⟩:= heftZ S A hp Z v P.odd_side (H i); let x:= spool G (t i) v; let W:= installed S.ratio (kite G P A)*ᵥ x; specialize hx (t i*P.L) W
     rw [regaled Y ht]; unfold narrate; rw [libAdd V ((-1:ℝ) • stitch T) hm (hY.const_smul (-1:ℝ)),libScale]; change library _ Y _ = library _ V _+(-1:ℝ)*narrate _ (stitch T) _; rw [regaled T hh']; unfold narrate; unfold Y V T player; erw [raftReads _ Z.rocket2 _ (VolAll _ (drip_cash ..) _ hg),volume_torque (g:=S.ratio) (drip_cash ..) Q hg, volume_torque (g:=S.ratio) hh Q hg,volume_torque (g:=S.ratio) hi p hS]; erw [ha,hL] at hx; change narrate _ Q _ = narrate _ Q _+(-1:ℝ)*narrate _ p W; have ht (a b c:ℝ) (h:c=a+b): a=c+(-1)*b:= by rw [h]; ring
     exact ht _ _ _ hx
end slide
end Script
end YM.OPE.Flume
