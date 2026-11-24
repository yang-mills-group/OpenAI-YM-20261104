import YM.OPE.Compatible.Mire.Rain
/-!
# Harmonic tests without spherical functions. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Sagebrush
open Function MeasureTheory Set Topology Metric Filter Lattice Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
open Extra.FD.OPE
open Next.Rank.Radian (dV stroll)
variable {x:E4}{k j m n:ℕ}{f g:E4→ℝ}{s:ℝ}
abbrev seg (f:E4→ℝ):= ContDiff ℝ ∞ f
lemma pure_multiply (hf:PureA n f)(hg:PureA k g): PureA (n+k) (f*g):=hf.bilinear hg (ContinuousLinearMap.mul ℝ ℝ)
lemma sumSeg (f:Axis→ E4→ℝ)(H:∀ i,seg (f i)):seg (∑ i, f i):=by
   rw [show (∑ i, f i)=(fun x=> ∑ i,f i x) from funext fun x=> Finset.sum_apply x _ f]; exact ContDiff.sum (fun i _=> H i)
lemma sph_der (hf:Spherical f (k+1))(i:Axis):Spherical (grad i f) k:=⟨hf.size.derive i,by rw [lap_derives hf.size.smooth,hf.harmonic,show grad i (0:E4→ℝ)=0 from funext fun x=>by simp [grad,D]]⟩
lemma lap_harm (hg:Spherical g n)(hf:seg f): lap (f*g)=lap f*g+(2:ℝ) • ∑ i:Axis, grad i f*grad i g:=by
   funext x; have he:=hg.size.smooth; have ht:=lap_pair hf he (ContinuousLinearMap.mul ℝ ℝ) x; rw [hg.harmonic] at ht
   change lap (f*g) x=(lap f x)*g x+ f x*(0:ℝ)+ 2*∑ i:Axis, grad i f x *grad i g x at ht
   rw [ht, mul_zero, add_zero,Pi.add_apply,Pi.smul_apply,Finset.sum_apply]; rfl
lemma zap : ends k (0:E4→ℝ)=0:=by induction k with | zero=> rfl | succ k ih=> rw [←ends_lap, show lap (0:E4→ℝ)=0 from SphereTest.lap_zero _]; exact ih
lemma silence (hf:PureA k f)(hg:Spherical g m)(he:k<m)(hh:k+m=2*j): ends j (f*g)=0:=by
    induction j generalizing f g k m with
    | zero=> omega
    | succ j ih=>
      cases m with
      | zero=>omega
      | succ m=>
        let Cw (i:Axis):=grad i f*grad i g; have hs(i):seg (Cw i):=(grad_diff_all hf.smooth i).mul (sph_der hg i).size.smooth; let S:= ∑ i, Cw i; have hp:seg S:=sumSeg _ hs
        rw [← ends_lap,lap_harm hg hf.smooth,ends_add j (show seg (lap f*g) from (lap_diff hf.smooth).mul hg.size.smooth) (show seg ((2:ℝ) • S) from hp.const_smul (2:ℝ)),ends_scale j hp,ends_sum _ _ _ (fun i _=>hs i)]
        have hx: ends j (lap f*g)=0:=by
           obtain rfl|rfl|hk:=show k=0 ∨ k=1∨ k≥ 2 by omega
           · rw [hf.zeroth,SphereTest.lap_zero]; rw [show (fun _ : E4=>(0:ℝ))=0 from rfl, zero_mul]; exact zap
           · have ht:lap f=0:=by
                funext x; unfold lap; refine Finset.sum_eq_zero (fun i _=>?_); have ha: PureA 0 (grad i f):=hf.derive i; rw [ha.zeroth]; simp [grad,D]
             rw [ht,zero_mul]; exact zap
           obtain ⟨l,hk'⟩:∃ l,k=l+2:=⟨k-2,by omega⟩
           subst k; exact ih hf.laplace hg (by omega) (by omega)
        rw [hx]; unfold Cw; cases k with
        | zero=>
          rw [hf.zeroth]; simp_rw [show ∀ i:Axis, grad i (fun _=> f 0)=(0:E4→ℝ) from fun i=> funext fun x=> by simp [grad,D],zero_mul, zap]; simp
        | succ k=>
          have ht(i:Axis): ends j (grad i f*grad i g)=0:=ih (hf.derive i) (sph_der hg i) (by omega) (by omega); simp_rw [ht]; simp
lemma ends_step (hf:seg f) (a:Axis): ends (k+1) (coordF a*f)=2*((k:ℝ)+1)*ends k (grad a f):=by
   induction k generalizing f with
   | zero=> rw [←ends_lap, show lap (coordF a*f)=coordF a*lap f+(2:ℝ) • grad a f from funext (lap_coordF_mul a hf)]; unfold ends; simp [coordF]
   | succ k ih=>
      have he:seg (grad a f):=grad_diff_all hf a; have ht:=lap_diff hf; rw [←ends_lap (k+1), show lap (coordF a*f)=coordF a*lap f+(2:ℝ) • grad a f from funext (lap_coordF_mul a hf)]; erw [ends_add _ (f:=coordF a*lap f) (g:=(2:ℝ)•grad a f) ((pure_coordF a).smooth.mul ht) (he.const_smul (2:ℝ)), ih ht, ends_scale (k+1) he, ← lap_derives hf,ends_lap k]; simp only [smul_eq_mul];push_cast;ring
lemma twist_d (l:List Axis) (hf:seg f)(a:Axis): grad a (dV l f)=dV l (grad a f):=by
   induction l with
   | nil=>rfl
   | cons i l ih=>
       change grad a (grad i (dV l f)) = grad i (dV l (grad a f))
       rw [←ih]; exact funext fun x=> grad_exchange (Next.Rank.Radian.stroll l hf.contDiffAt) _ _
def mon : List Axis→ E4→ℝ | []=>1 | a::l=> coordF a*mon l
lemma pureMon (l:List Axis):PureA l.length (mon l):=by
   induction l with
   | nil=> exact ⟨contDiff_const,fun x t=> (by change (1:ℝ)=t^(0:ℕ)*1; ring)⟩
   | cons a l ih=> change PureA (l.length+1) (coordF a * mon l); rw [add_comm]; exact pure_multiply (pure_coordF a) ih
def mash (k:ℕ):ℝ:=2^k*k.factorial
lemma roster (l:List Axis)(hf:Spherical f l.length): ends l.length (mon l*f)= mash l.length*dV l f 0:=by
    induction l generalizing f with
    | nil=> change ends 0 ((1:E4→ℝ)*f)=mash 0*f 0; simp [mash,ends]
    | cons i l ih=>
      let k:=l.length; have hp:=pureMon l; have hX:=hf.size.smooth
      rw [mon,mul_assoc,List.length_cons,ends_step (f:=mon l*f) (hp.smooth.mul hX),show dV (i::l) f=dV l (grad i f) from twist_d _ hX i]
      have he:grad i (mon l*f)= grad i (mon l)*f+mon l*grad i f:= funext fun x=>Gp (mon l) f hp.smooth.contDiffAt hX.contDiffAt i -- syntax replace
      erw [he,ends_add _ ((grad_diff_all hp.smooth i).mul hX) (hp.smooth.mul (grad_diff_all hX i)), ih (sph_der hf i)]
      suffices e: ends k (grad i (mon l)*f)=0 by erw [e,zero_add]; unfold mash; rw [pow_succ,Nat.factorial_succ];push_cast;ring
      cases l with
      | nil=> change ends 0 (grad i (1:E4→ℝ)*_)=_; unfold ends; simp [grad,D]
      | cons a l=> apply silence (k:=l.length) (hp.derive i) hf (by simp) (by unfold k; simp;omega) -- k
end YM.OPE.Sagebrush
