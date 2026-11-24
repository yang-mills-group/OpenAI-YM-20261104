import YM.WilsonCoeffUV.Kinetic.Variance
/-!
# Formal stationary extraction

Absolute determinant charts at REAL fixed background, then normalized
Taylor. This theorem does the full internal integral (`Wick`), not saddle
approximations to a clipped density. Only degree two promoted to thermal.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue.Cameo
open Matrix Function PowerSeries Filter
open scoped Topology ContDiff BigOperators
variable {U V:Type}[Fintype U][DecidableEq U][Fintype V][DecidableEq V]
variable {f g : Lawn (U⊕V)→ℝ}{K:Matrix U U ℝ}{θ:Lawn (U⊕V)→Lawn U} {L H P E:Ink (U⊕V)}{B:Ink V}

-- cross coefficient chart
structure Hearth (K:Matrix U U ℝ)(B:Ink V)(P E H:Ink (U⊕V)) : Prop where
   monic: constantCoeff E=constantCoeff (bodyQ V K+holdUp U B)
   ho : constantCoeff H=0
   price : P= bodyQ V K+holdUp U B-E+H
omit [DecidableEq U] [Fintype V] [DecidableEq V] in
lemma Hearth.zero (h:Hearth K B P E H): constantCoeff P=0:=by rw [h.price,map_add,h.ho, map_sub,h.monic,sub_self,add_zero]

def blaze (θ:Lawn (U⊕V)→Lawn U)(H:Ink (U⊕V))(g:Lawn (U⊕V)→ℝ): Prop := (motionJ (spool θ)).det*raiseE (retool θ H)=raiseE (jet g)
lemma blaze_new {u x:Lawn (U⊕V)→ℝ}(h:Green x)(p:x 0=0)(v:Fathom f θ E)(hx:Green u)(hu:u 0=0) (z:∀ᶠ w:Lawn (U⊕V) in 𝓝 0,(edgeM θ w).det*Real.exp (u (spider θ w))= Real.exp (x w)) : blaze θ (jet u) x:=by
   have hy:=spider_green v.θp; have hz:=spider_zero v.θo; let d w:=(edgeM θ w).det
   rw [blaze, ← solar_motion θ v.θp v.θo,pivot θ,traveling (spider θ) hy hz u hx, ←literal_exp h p];
   have hG:Green (u ∘ spider θ):= (show ContDiffAt ℝ ω u (spider θ 0) from hz.symm ▸ hx).comp _ hy
   rw [← literal_exp hG (by simp [hz,hu]),← jet_mul (f:=d) (by apply MGreen.det; exact edge_green θ v.θp) (g:=fun w=>Real.exp ((u ∘ spider θ) w)) hG.exp]; exact jet_congr z

def blanket (K:Matrix U U ℝ)(B:Ink V) (P:Ink (U⊕V))(g:Lawn (U⊕V)→ℝ) := bodyQ V K+holdUp U B-P+jet g
lemma baptism (h:Fathom f θ E)(u:Hearth K B P E H)(e:K.transpose=K)(p:IsUnit K.det)(d:Lawn (U⊕V)→ℝ)(hd:d 0=0)(hv:blaze θ H d):
    let W:= retool θ E; let Q:=blanket K B W d
    Hearth K B Q W (jet d) ∧ Wick V K⁻¹ (raiseE P)=Wick V K⁻¹ (raiseE Q):=by
   intro W Q
   obtain ⟨hc,hr⟩:=funded h K e p u.monic
   have ht:constantCoeff (jet d)=0:=by rw [jet_lead,hd,map_zero]
   refine ⟨⟨hc,ht,rfl⟩,?_⟩
   have he₀:K⁻¹.transpose=K⁻¹:=by rw [transpose_nonsing_inv,e]
   have he₁:K=(1:Matrix U U ℝ).transpose*K*1:=by simp
   have he₂:= W_covariance he₀ e (Matrix.mul_nonsing_inv K p) he₀ (raiseE P) (1:Matrix U U ℝ) (by rw [Matrix.det_one]; exact isUnit_one) he₁ (by simp) (spool θ) path hr
   let T:=retool θ; let M:=Matrix.det (motionJ (spool θ)); let J:=bodyQ V K; let U':=J-T J
   have hU':constantCoeff U'=0:=local_zero_roll _ _ hr he₁
   rw [Matrix.det_one,map_one,train_id,RingHom.id_apply,one_mul] at he₂
   rw [← he₂]; apply congr_arg (Wick V K⁻¹); change M*(raiseE U'*T (raiseE P))=_
   let o:=holdUp U B
   let F:=J+o-E
   have hp: P=F+H:=u.price
   have hf: U'+T F=J+o-W:=by unfold U' F; simp only [map_sub,map_add,show T o=o from retool_tall θ B]; change _=J+o-T E; abel
   have hx:constantCoeff F=0:=by unfold F; rw [map_sub]; change constantCoeff (_+_)-_=0; rw [u.monic]; simp only [J,o,sub_self]
   have hz:constantCoeff (T F)=0:= floor_pres (reroll_X _ _) hx
   have hh : M*raiseE (T H)=raiseE (jet d):=hv
   rw [hp, raise_add hx u.ho,map_mul,raise_map T (retire θ) hx,raise_map T (retire θ) u.ho,show Q=U'+T F+jet d from by rw [hf]; rfl, raise_add (by simp [hU',hz]) ht,raise_add hU' hz,← hh]; ring
-- auxiliary whitening Jacobian

def wages (P:Lawn (U⊕V)→ℝ)(Q:Lawn V→Matrix U U ℝ) (x:Lawn (U⊕V)):=
   P (spider (caulk Q) x)+ Real.log (Q (rightArm x)).det
lemma gleam {Q:Lawn V→Matrix U U ℝ}(h:MGreen Q)(p:Q 0=1)(e:Green f): Green (wages f Q):=by
   have H: Green fun x=>Real.log (Q x).det:= (h.det).log (by rw [p,Matrix.det_one]; simp)
   exact (sailM_green h e).add (H.comp (f:=rightArm (U:=U)) 0 rightGreen)
omit [Fintype V] [DecidableEq V] in
lemma lilt {Q:Lawn V→Matrix U U ℝ}(p:Q 0=1) (e:f 0=0): wages f Q 0=0:=by rw [wages,spider_zero (caulk_zero _),rightZero,p,e,Matrix.det_one]; simp
lemma shaft {h:Lawn (U⊕V)→ℝ}{Q:Lawn V→Matrix U U ℝ}(p:MGreen Q)(t:Q 0=1)(he:Fathom f (caulk Q) E)(v:Green h)(z:h 0=0): blaze (caulk Q) (jet h) (wages h Q):=by
   refine blaze_new (gleam p t v) (lilt t z) he v z ?_
   have hu:= (p.det.comp (f:=rightArm (U:=U)) 0 rightGreen).continuousAt.eventually (lt_mem_nhds (show 0<(fun x:Lawn (U⊕V)=> (Q (rightArm x)).det) 0 by change 0<(Q 0).det; rw [t,Matrix.det_one]; simp))
   filter_upwards [caul_fee p, hu] with w wh hw using by change 0 < (Q (rightArm w)).det at hw; rw [wh,wages,Real.exp_add,Real.exp_log hw,mul_comm (Real.exp _)]

-- scalar identities and low grade in final expression
omit [Fintype V] [DecidableEq V] in
lemma log_health {f p:Ink V} (he:constantCoeff p=1)(h:constantCoeff f=0) : logOf (raiseE f*p)=f+logOf p:=by
    have hp : constantCoeff (raiseE f * p)=1:= by simp [he,raise_one h];
    have hq:=constantCoeff_logOf he; apply raise_inj (constantCoeff_logOf hp) (by simp [h,hq]); rw [raise_add h hq,raising_log hp,raising_log he]
lemma essenceR {G:Ink (U⊕V)}(_:K.transpose=K)(hk: Green g)(h:Hearth K B P G (jet g)) (q: BrushGrade (faintRest K G)) :
    let w:= projectZero G-jet (baseP g)
    Mist id (B-logOf (Wick V K⁻¹ (raiseE P))-w):=by
    intro w
    let b₀:=baseP g
    let T:= (-faintRest K G)+(jet g-holdUp U (jet b₀)); let A:= B-w
    have ht:=cc_proj h.monic; rw [map_add projectZero,project_up,moonZero,zero_add] at ht
    have hb:=h.ho
    have he:constantCoeff (jet b₀)=0:=by have hu := floor_pres (T:=projectZero) (by simp [projectZero]) hb; rwa [projectBasis hk] at hu
    have hv: Green (b₀∘rightArm (U:=U)):= by apply ContDiffAt.comp (f:=rightArm) _ _ rightGreen; rw [rightZero]; exact immersed hk
    have ha: constantCoeff A=0:= by unfold A w; rw [map_sub, map_sub, ht, he]; simp
    have hx : P=T+holdUp U A:= by unfold T A w faintRest; dsimp only [b₀]; rw [map_sub,map_sub]; rw [h.price]; abel
    have hz:constantCoeff T=0:=by have he:=floor_pres (T:=holdUp U) hold_X' ha; have hq:=h.zero; rw [hx,map_add,he,add_zero] at hq; exact hq
    have hh:Mist id (logOf (Wick V K⁻¹ (raiseE T))) := by
        apply faux _ hz; let f:= g-(b₀ ∘ rightArm)
        have hm: Green f := hk.sub hv
        have h' : jet g-holdUp U (jet b₀)=jet f:=by unfold f; rw [jet_sub hk hv,liftBasis (immersed hk)]
        have H' : projectZero (jet f)=0:=by rw [← h',map_sub,project_up,projectBasis hk]; unfold b₀; rw [sub_self]
        have he:= BrushGrade.mesh hm (by rw [H']; exact Equal.refl _ _)
        have hR: Mist (U:=V) Sum.inr (jet g-holdUp U (jet b₀)):= by rw [h']; exact ⟨he.1,he.2⟩
        have hg:=Mist.add ((show Mist Sum.inr (faintRest K G) from ⟨q.1,q.2⟩).neg) hR; exact ⟨hg.first,hg.second⟩
    have hm : Wick V K⁻¹ (raiseE P)=raiseE A* Wick V K⁻¹ (raiseE T):=by
        rw [hx,raise_add hz (floor_pres hold_X' ha),←raise_map (holdUp U) (by rw [hold_X']; simp) ha, W_param]; rw [mul_comm]
    rw [hm,log_health (glaze_log _ hz) ha,
        show B-(A+logOf (Wick V K⁻¹ (raiseE T)))-w= -(logOf (Wick V K⁻¹ (raiseE T))) by unfold A; abel]
    exact hh.neg

-- returned analytic thermo included Jet constant separate

def vineT (f g : Lawn (U⊕V)→ℝ)(y:Lawn V) := -(baseP g y)+1/2*Real.log (sandH f y).det
lemma vine_green (h:Green f)(p:Green g)(u:0<(sandH f 0).det): Green (vineT f g):= ContDiffAt.add (show ContDiffAt ℝ ω (fun x=> -(baseP g x)) 0 from (immersed p).neg) (ContDiffAt.mul contDiffAt_const ((sand_green h).det.log u.ne'))
lemma figure_fee (p:sandH f 0=K)(hv:0<K.det)(h:Green f) (hx:Green g):
    Equal 3 (jet (vineT f g-fun _ => 1/2*Real.log K.det)) (-jet (baseP (wages g (polarH K (sandH f))))):=by
    let M:= polarH K (sandH f)
    have hg: Green (fun x=>Real.log (sandH f x).det):=(sand_green h).det.log (by rw [p]; exact hv.ne')
    let T (x:Lawn V):= (-1/2:ℝ)*(Real.log (sandH f x).det-Real.log K.det)
    let d:= baseP g; let a x:=Real.log (M x).det
    have he : Equal 3 (jet a) (jet T):= shareD (sandH f) K (sand_green h) p (sand_sym h) hv
    have hz: Green a:= ((polar_green K (sand_green h)).det).log (by rw [polar_one p,det_one]; simp)
    have hd:=immersed hx; have hh: Green T:= ContDiffAt.mul contDiffAt_const (hg.sub contDiffAt_const)
    rw [show (vineT f g-fun _ => 1/2*Real.log K.det) = -(d+T) from funext (fun i=>by simp only [vineT,Pi.sub_apply, Pi.neg_apply,Pi.add_apply]; unfold T d; ring)]
    have ht: baseP (wages g M)=d+a:=by funext x; change wages _ _ _= _+_; unfold wages; rw [caul_spin]; rfl
    have hm: Green (d+T):=hd.add hh
    change Equal _ (jet _) (-jet (baseP (wages g M))); rw [ht, jet_neg hm,jet_add hd hz,jet_add (f:=d) hd hh]; intro i p; simp only [map_neg,map_add, he _ p]; rfl
omit [Fintype V] [DecidableEq V] in
lemma MistD {x:Ink V} (h:Dark 3 x): Mist id x:= ⟨fun i=> ((h.stave i).faint (by omega)),fun i j=> ((h.stave j).stave i)⟩

/-- Stationary extraction. Classical positive ranks through projected horizon,
normalized relative angular formula. Φ scalar response separated; no output
at positive couplings of the interacting integral. -/
theorem vane (h:Hearth K B P E H)(q:Fathom f θ E)(e:K.transpose=K)(k:0<K.det)(p:Green g)(z:g 0=0)(u:blaze θ H g):
    let C:= flash (sprig (baseP f) 2); let Z:=jet (vineT f g-fun _=>1/2*Real.log K.det)
    sandH f 0=K ∧ Mist id (B-logOf (Wick V K⁻¹ (raiseE P))-(C+Z)) :=by
    intro C Z
    have ht:=centerK K q e h.monic; have hD:= k.ne'.isUnit
    obtain ⟨H,Y⟩:= baptism q h e hD g z u
    let Q:=retool θ E ; let M:= polarH K (sandH f); let a:=caulk M; let D:= wages g M; let X:= polar_green K (sand_green q.sta)
    have hx:=fathomed q ht
    obtain ⟨O,V'⟩:= baptism (P:=blanket K B Q g) hx H e hD D (lilt (polar_one ht) z) (shaft X (polar_one ht) hx p z)
    rw [Y,V']; let T:=retool a Q; have he:projectZero T=C:=by
        have hh:=projectBasis hx.sta
        rw [← hx.shine,map_mul,map_pow,show projectZero (PowerSeries.X:Ink (U⊕V))=PowerSeries.X by simp [projectZero]] at hh
        have hp: baseP (f∘spider a) =baseP f:=by funext i; simp only [baseP,Function.comp_apply, a, caul_spin]
        change PowerSeries.X^2 * projectZero T=_ at hh
        rw [hp] at hh
        unfold C; rw [sprig_flash]; ext1 i; rw [coeff_mk,← hh,coeff_X_pow_mul'] ; simp
    let S:= blanket K B T D; let d:=baseP D
    have hp : Mist id (B-logOf (Wick V K⁻¹ (raiseE S))-(projectZero T-jet d)) := essenceR (g:=D) e (gleam X (polar_one ht) p) O (fath_mask q ht hD).2
    rw [he] at hp
    have hh:Mist id (Z-(-jet d)):= MistD (scotch (figure_fee ht k q.sta p));
    refine ⟨ht,?_⟩; convert! hp.add (hh.neg) using 1; abel
end YM.WilsonCoeffUV.Blue.Cameo
