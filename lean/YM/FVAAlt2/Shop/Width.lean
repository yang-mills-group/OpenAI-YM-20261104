import YM.FVAAlt2.Shop.Grad
import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.Park
/-!
# Plane jet on a link and a curl. Each leg MAY be integrated along
 its positive links: multiplier is smooth in each frequency, `=1` at zero
 frequency, same for EVERY link of that type. This is enough for Taylor
 leading order Read, but **not** a convention that could replace the
 stencil in the higher loop graphs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Shop
open Function Finset Filter Topology Wilson Labels Source Source.Drops
open Comparison.Stencils.Corona (Crumb Primary Binds Tally demonstrates act_simple plated scape)
open MS MS.Koszul MS.Native MS.Landau MS.Landau.Detect MS.Plane MS.Tone MS.Theater
open MeasureTheory intervalIntegral InnerProductSpace MS.Momentum MS.Heat
open Lattice
open Work.G03 (castPos castPos_step)
open scoped Interval Topology ContDiff
variable {G:Gauge}{d k:ℕ}{F:Labels.Frame G d}
local notation "C"=> Comparison.Stencils.Corona.act
local notation "I"=> Complex.I
local notation "Θ"=> Lane4 G
abbrev cpar (p:QP)(x:E4):ℝ:= inner ℝ (fixF p) x
abbrev exteriorDir (x:Θ): Prop:= ∃ i:Axis,x.1.1=Landau.gauge i
lemma payray (p q:QP)(t:ℝ): bill (t • p) q= Complex.exp ((I*(cpar p (fixF q):ℂ))*(t:ℂ)):= by
 have h : cpar p (fixF q)=Momentum.pairing p q:=by unfold cpar Momentum.pairing; rw [PiLp.inner_apply]; simp only [RCLike.inner_apply,starRingEnd_apply,star_trivial]; simp_rw [mul_comm];rfl
 rw [h]; unfold bill Momentum.pairing; congr 1; simp_rw [Pi.smul_apply, smul_eq_mul,mul_assoc (t:ℝ), ← Finset.mul_sum]; push_cast; ring
lemma derivPower (r:ℂ)(n:ℕ)(t:ℝ): iteratedDeriv n (fun t:ℝ=>Complex.exp (r*(t:ℂ))) t=r^n*Complex.exp (r*(t:ℂ)):=by
 induction n generalizing t with
 | zero=> simp
 | succ n ih=>
   rw [iteratedDeriv_succ, funext ih]
   let f (t:ℝ):=r*(t:ℂ); have hh: HasDerivAt f r t:= by convert! (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (𝕜:=ℝ) t (hasDerivAt_id' t)).const_mul r using 1; simp
   rw [show deriv _ t =_ from ((hh.cexp).const_mul (r^n)).deriv]; rw [pow_succ];unfold f;ring
lemma read_phase (p q:QP)(n:ℕ): reading n (fun t:ℝ=>bill (t • p) q)=(amount n:ℂ) * (I*(cpar p (fixF q):ℂ))^n:=by simp_rw [reading,payray]; rw [derivPower]; simp [Complex.real_smul,amount]

lemma frame_track (x:Edge Cover)(t:ℝ): Theater.out (track x t)= embed x.1+t • embed (step x.2):= by
 funext u; unfold track; rw [map_add,map_smul]; simp only [ Theater.out, WithLp.linearEquiv_apply ]; simp [emb_step,Work.G03.castPos,basis]; simp [Pi.single_apply,embed]

lemma inter (F:ℝ×ℝ→ℂ)(h:ContDiff ℝ ∞ F)(j:ℕ): reading j (fun t:ℝ=>∫ s:ℝ in 0..1,F (s,t))=∫ s:ℝ in 0..1, reading j (fun t:ℝ=> F (s,t)):=by
 unfold reading;
 let L:=( ContinuousMultilinearMap.apply ℝ (fun _:Fin j=>ℝ) ℂ (fun _=> (1:ℝ)) );
 let Q (s:ℝ):= iteratedFDeriv ℝ j (fun t:ℝ=> F (s,t)) 0
 have hQ: Continuous Q:= by
     unfold Q; simp_rw [ extDer h ]; exact (ContinuousMultilinearMap.compContinuousLinearMapL (F:=ℂ) (fun _:Fin j=> ContinuousLinearMap.inr ℝ ℝ ℝ)).continuous.comp ((h.continuous_iteratedFDeriv (m:=j) (by exact_mod_cast le_top)).comp (by fun_prop : Continuous fun r:ℝ=> (r,(0:ℝ))))
 have he : L (∫ s:ℝ in 0..1,Q s)=∫ s:ℝ in 0..1,L (Q s) := ( L.intervalIntegral_comp_comm (hQ.intervalIntegrable _ _)).symm -- orientation
 change amount j • L (iteratedFDeriv ℝ j (fun t:ℝ=> desk F (1,t)) 0)=∫ s:ℝ in 0..1, amount j • L (Q s);
 rw [comp_iter h, intervalIntegral.integral_smul]; exact congr_arg _ he

lemma mind_dir (p:QP)(F:ℝ→QP)(h:ContDiff ℝ ∞ F): ContDiff ℝ ∞ (fun y:ℝ×ℝ=>bill (y.2 • p) (F y.1)):=by
 unfold bill Momentum.pairing; simp_rw [Pi.smul_apply];
 refine ContDiff.cexp ( contDiff_const.mul ( Complex.ofRealCLM.contDiff.comp (show ContDiff ℝ ∞ (fun y:ℝ×ℝ=> Momentum.pairing (y.2 • p) (F y.1)) from ?_) ) ); unfold Momentum.pairing; apply ContDiff.sum
 intro i _; simp_rw [Pi.smul_apply]; exact (contDiff_snd.smul contDiff_const).mul ((contDiff_pi.mp h i).comp contDiff_fst)

def iface (p:QP)(b:Axis)(t:ℝ):= ∫ s:ℝ in 0..1,bill (t • p) ((s-1/2) • embed (step b))
lemma ifaceSmooth (p:QP)(b:Axis): ContDiff ℝ ∞ (iface p b):=
 (park (mind_dir p (fun s:ℝ=>(s-1/2) • embed (step b)) (by fun_prop))).comp (show ContDiff ℝ ∞ (fun t:ℝ=>((1:ℝ),t)) by fun_prop)
lemma iface0 (p:QP)(b:Axis):iface p b 0=1 := by unfold iface; simp

def lensw (x:Θ)(t:ℝ): ℂ:= match x.1.1.1 with | none=>1| some b=> iface x.2 b t
lemma lenswSmooth (x:Θ): ContDiff ℝ ∞ (lensw x):=by unfold lensw; split; exact contDiff_const; exact ifaceSmooth ..
lemma lensw0 (x:Θ):lensw x 0=1:=by unfold lensw; split; rfl; exact iface0 ..
def hits (x:Θ)(t:ℝ):Θ:= (x.1,t • x.2)
variable (p:QP) (b:Axis) (a:Edge Cover) (r k:G.ColorIndex)
abbrev ψ (i:Axis)(v:G.ColorIndex) (p:QP): Θ:= Tone.Frame.waveForm p i v
lemma edge_zone (t:ℝ): lensw (ψ a.2 r p) t * onew (a,r) ( hits (ψ a.2 r p) t )=
  ∫ s:ℝ in 0..1,bill (t • p) (Theater.out (track a s)):=by
 unfold lensw; dsimp only [ψ,Tone.Frame.waveForm,Landau.gauge]; change iface _ _ _ * paywave ((Landau.gauge a.2, r), t • p) ((Landau.gauge a.2, r), a.1)=_; rw [ show paywave _ _ =_ from Tone.pw (Landau.gauge a.2,r) a.1 (t • p),iface,mul_comm,← intervalIntegral.integral_const_mul]; -- need prove interior identical exactly
 refine integral_congr fun u _=>?_ ; rw [← rightadd, frame_track]; congr 1; rw [Landau.gauge,here_a, add_assoc, ← add_smul]; ring_nf
lemma edge_s (i:Mind G Cover)(x:Θ): ContDiff ℝ ∞ (fun t:ℝ=>onew i (hits x t)):= by
 unfold onew paywave hits; dsimp only;  exact contDiff_const.mul (Lifting.bankForm x.2 _)
-- weighted derivative order with onew
lemma edge_mask (p:Θ)(i:Mind G Cover)(ht:p.1≠(Landau.gauge i.1.2,i.2))(t:ℝ): onew i (hits p t)= 0:= by
   apply Classical.byContradiction; intro e; exact ht (sees_p i (hits p t) e)

lemma loanG(n:ℕ) : reading n (fun t:ℝ=>lensw (ψ a.2 r p) t * onew (a,r) ( hits (ψ a.2 r p) t ))=
  I^n*(↑(coverage n (speak n a.2 p (cl G r)) a r):ℂ):=by
   simp_rw [edge_zone];
   let F (y:ℝ×ℝ):=bill (y.2 • p) (Theater.out (track a y.1))
   have h:ContDiff ℝ ∞ F:=mind_dir p (fun x=> Theater.out (track a x)) ((Theater.out.toLinearMap.toContinuousLinearMap.contDiff).comp (trackSmooth a))
   rw [ show reading n _= _ from inter F h n ]; unfold F;
   let L: G.Color→L[ℝ] ℂ := Complex.ofRealCLM ∘L EuclideanSpace.proj r
   let q:=speak n a.2 p (cl G r); rw [show (↑(coverage n q a r):ℂ)=∫ s:ℝ in 0..1,L ((Tensor.diagonal (q.val a.2) (track a s))) from (L.intervalIntegral_comp_comm (cover_frame a q)).symm,← intervalIntegral.integral_const_mul ]; refine integral_congr fun x _=> ?_; dsimp only; rw [read_phase]; dsimp only [L,Tensor.diagonal,ContinuousLinearMap.comp_apply,q,speak]; rw [Theater.wearing]; simp [cl,amount, cpar, fixF]; ring -- inspect

lemma loanAll (n:ℕ) : reading n (fun t:ℝ=>lensw (ψ b k p) t * onew (a,r) ( hits (ψ b k p) t )) = I^n * (↑(coverage n (speak n b p (cl G k)) a r):ℂ):= by
 classical
 by_cases h:k=r; swap
 · simp_rw [edge_mask (ψ b k p) (a,r) (show (ψ b k p).1≠(Landau.gauge a.2,r) from fun ht=>h (Prod.ext_iff.mp ht|>.2)),mul_zero]
   have hz : coverage n (speak n b p (cl G k)) a r=0:= by
       rw [show coverage n _ _ r=∫ s:ℝ in 0..1, Tensor.diagonal ( (speak n b p (cl G k)).val a.2 ) (track a s) r from ((EuclideanSpace.proj (ι:=G.ColorIndex) (𝕜:=ℝ) r).intervalIntegral_comp_comm (cover_frame a (speak n b p (cl G k)))).symm];
       by_cases ht:b=a.2; · subst b; unfold speak Tensor.diagonal; simp_rw [wearing]; simp [Ne.symm h, cl]
       unfold speak; rw [away n _ _ (Ne.symm ht)]; simp [Tensor.diagonal]
   rw [hz]; simp [reading]
 subst k; by_cases hb:b=a.2; subst b; exact loanG p a r n
 simp_rw [edge_mask (ψ b r p) (a,r) (show (ψ b r p).1≠(Landau.gauge a.2,r) by simp [hb,ψ,Tone.Frame.waveForm, Landau.gauge]),mul_zero]; unfold coverage speak; rw [away n _ _ (Ne.symm hb)]; simp [Tensor.diagonal,reading] -- rw binder caution
end YM.FVAAlt2.Shop
