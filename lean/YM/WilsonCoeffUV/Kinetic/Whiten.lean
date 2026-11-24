import YM.WilsonCoeffUV.Kinetic.TaylorFirst
/-!
# Fixed angular Gaussian whitening jet

No spectral roots. Symmetric perturbation frozen via second matrix
Neumann step. Leaves a remainder of order 3 from the H sector, dropped
ONLY in the fixed second-rank comparison. Jacobian det and real log paid
at normalized constants.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue.Cameo
open Matrix Function PowerSeries Filter
open scoped Topology ContDiff BigOperators
variable {U V: Type*}[Fintype U] [DecidableEq U][Fintype V]

section pads
variable {Q R : Matrix U U ℝ}{F H:Lawn V→Matrix U U ℝ}
def MGreen (F:Lawn V→Matrix U U ℝ) := ∀ i j, Green fun x:Lawn V=>F x i j
def jPrint (F:Lawn V→Matrix U U ℝ): Matrix U U (Ink V):= of fun i j=> jet fun x=>F x i j
omit [Fintype U] [DecidableEq U] in
lemma MG_const (P:Matrix U U ℝ) : MGreen (fun _:Lawn V=>P):= fun _ _=>contDiffAt_const
omit [Fintype U] [DecidableEq U] in
lemma MGreen.plus (h:MGreen F)(p:MGreen H): MGreen (fun x=>F x+H x):= fun i j=> (h i j).add (p i j)
omit [Fintype U] [DecidableEq U] in
lemma MGreen.sub (h:MGreen F)(p:MGreen H): MGreen (fun x=>F x-H x):=fun i j=>(h i j).sub (p i j)
omit [Fintype U] [DecidableEq U] in
lemma MGreen.flip (h:MGreen F) : MGreen (fun x=>(F x).transpose):=fun i j=>h j i
omit [Fintype U] [DecidableEq U] in
lemma MGreen.μ (u:ℝ)(h:MGreen F):MGreen (fun x=>u • F x):= fun i j=>by simp only [Matrix.smul_apply]; exact ContDiffAt.const_smul u (h i j)
omit [DecidableEq U] in
lemma MGreen.times (h:MGreen F)(p:MGreen H): MGreen (fun x=>F x*H x):= fun i j=> ContDiffAt.sum (fun k _=>(h i k).mul (p k j))
omit [Fintype U] [DecidableEq U] in
lemma jPlus (h:MGreen F)(p:MGreen H): jPrint (fun x=>F x+H x)=jPrint F+jPrint H:=by ext1 i j; exact jet_add (f:=fun x=>F x i j) (g:=fun x=>H x i j) (h i j) (p i j)
omit [Fintype U] [DecidableEq U] in
lemma jSub (h:MGreen F)(p:MGreen H): jPrint (fun x=>F x-H x)=jPrint F-jPrint H:=by ext1 i j; exact jet_sub (f:=fun x=>F x i j) (g:=fun x=>H x i j) (h i j) (p i j)
omit [Fintype U] [DecidableEq U] in
lemma jMu (u:ℝ)(h:MGreen F): jPrint (fun x=>u•F x)=realS (U:=V) u • jPrint F:=by ext1 i j; exact jet_mul (f:=fun _:Lawn V=>u) (g:=fun x=>F x i j) contDiffAt_const (h i j) |>.trans (by rw [jet_const]; rfl)
omit [DecidableEq U] in
lemma jTimes (h:MGreen F)(p:MGreen H): jPrint (fun x=>F x*H x)=jPrint F*jPrint H:=by
   ext1 i j; let W (k:U):Lawn V→ℝ:=(fun x=> F x i k)*(fun x=> H x k j); change jet (fun x=>(F x*H x) i j)=_
   rw [show (fun x=>(F x*H x) i j)=∑ k,W k from funext (fun x=> by rw [Finset.sum_apply]; rfl),jet_sum Finset.univ W (fun k _=>(h i k).mul (p k j))]
   exact Finset.sum_congr rfl fun k _=> jet_mul (f:=fun x=>F x i k) (g:=fun x=> H x k j) (h i k) (p k j)
omit [Fintype U] [DecidableEq U] in
lemma jConst (Q:Matrix U U ℝ) : jPrint (fun _:Lawn V=>Q)=Q.map realS:= by ext1 i j; exact jet_const (Q i j)
omit [Fintype U] in
lemma jOne : jPrint (fun _ :Lawn V=>(1:Matrix U U ℝ))=1:=by rw [jConst]; simp
omit [Fintype U] [DecidableEq U] in
lemma jFlip (_h:MGreen F)(_p:MGreen H)(v:F=ᶠ[𝓝 0] fun x=>(H x).transpose): (jPrint F).transpose=jPrint H:=by ext1 i j; exact jet_congr (v.mono fun x e=> show F x j i=H x i j from congr_fun (congr_arg (fun T:Matrix U U ℝ => T j) e) i)
-- analytic determinant germs
lemma jet_prod {α: Type*}(s:Finset α){F:α→ Lawn V→ℝ}(h:∀ i∈s,Green (F i)): jet (∏ i∈s,F i)= ∏ i∈s,jet (F i):=by
    classical
    induction s using Finset.induction_on with
    | empty=> simp only [Finset.prod_empty]; simpa using! jet_const (U:=V) 1
    | @insert i s p ih=>
       have hx j (e:j∈s):= h j (Finset.mem_insert_of_mem e)
       have ht:Green (∏ j∈s,F j):= by unfold Green; rw [show (∏ j∈s,F j)=fun x=>∏ j∈s,F j x from funext fun x=> Finset.prod_apply ..]; exact contDiffAt_prod hx
       rw [Finset.prod_insert p,Finset.prod_insert p,jet_mul (h i (Finset.mem_insert_self ..)) ht, ih hx]
lemma MGreen.det (p:MGreen F): Green fun x=>(F x).det:=by
    unfold Green; simp only [Matrix.det_apply']; exact ContDiffAt.sum (fun i _ => ContDiffAt.mul contDiffAt_const (contDiffAt_prod (fun j _=>p _ _)))
lemma jDets (p:MGreen F): jet (fun x=>(F x).det)=(jPrint F).det:=by
    let v (i:Equiv.Perm U):ℝ:= ((Equiv.Perm.sign i:ℤ):ℝ); let w (i:Equiv.Perm U):Lawn V→ℝ:=∏ j:U, fun x=>F x (i j) j
    simp only [Matrix.det_apply']; rw [show (fun x=>∑ i:Equiv.Perm U,_) = ∑ i:Equiv.Perm U,(fun _:Lawn V=>v i)*w i from ?_]
    · have ht (i:Equiv.Perm U):Green (w i):= by unfold w Green; rw [show (∏ j:U,fun x:Lawn V=> F x (i j) j)=fun x=>∏ j:U,F x (i j) j from funext fun x=> Finset.prod_apply ..]; exact contDiffAt_prod (fun j _=>p _ _)
      rw [jet_sum Finset.univ (fun i=>(fun _:Lawn V=>v i)*w i) (fun i _=>ContDiffAt.mul contDiffAt_const (ht i))]; refine Finset.sum_congr rfl fun i _=>?_
      rw [jet_mul (f:=fun _ : Lawn V=>v i) contDiffAt_const (ht i),jet_const,show jet (w i)=_ from jet_prod (V:=V) (α:=U) (F:=fun j x=>F x (i j) j) Finset.univ (fun j _ =>p _ _)]; unfold v; rw [map_intCast]; rfl
    funext x; rw [Finset.sum_apply]; refine Finset.sum_congr rfl fun i _=>?_ ; simp only [Pi.mul_apply, w,v,Finset.prod_apply]
lemma cones {R:Type*}[CommRing R]{n:ℕ} {ι:Type*}(s:Finset ι)(f g:ι→PowerSeries R)(p:∀ i∈s,Equal n (f i) (g i)): Equal n (∏ i∈s,f i) (∏ i∈s,g i):=by
       classical
       induction s using Finset.induction_on with
       | empty=> simp only [Finset.prod_empty]; exact Equal.refl (1:PowerSeries R) n
       | @insert i s t ih=> rw [Finset.prod_insert t,Finset.prod_insert t]; exact (p i (Finset.mem_insert_self ..)).mul (ih fun j k=> p j (Finset.mem_insert_of_mem k))
set_option maxHeartbeats 700000 in
lemma Equal.conic {R:Type*}[CommRing R] {n:ℕ} (F G:Matrix U U (PowerSeries R))(h:∀ i j,Equal n (F i j) (G i j)): Equal n F.det G.det:=by

    simp only [Matrix.det_apply']; intro i t; rw [map_sum,map_sum]; apply Finset.sum_congr rfl; intro j _; exact ((Equal.refl (((Equiv.Perm.sign j:ℤ):PowerSeries R)) n).mul (cones (Finset.univ (α:=U)) (fun i:U=>F (j i) i) (fun i:U=>G (j i) i) (fun i _=> h (j i) i))) i t

-- polar polynomials. use truncated Equal.
def Dips (Q:Matrix U U ℝ)(F:Lawn V→Matrix U U ℝ)(x:Lawn V):= Q⁻¹*(F x-Q)
def polarH (Q:Matrix U U ℝ)(F:Lawn V→Matrix U U ℝ)(x:Lawn V) := let M:= Dips Q F x
    1+(-1/2:ℝ) • M+(3/8:ℝ) • (M*M)
omit [Fintype V] in
lemma dips_zero (h:F 0=Q):Dips Q F 0=0:=by simp [Dips,h]
omit [Fintype V] in
lemma polar_one (h:F 0=Q):polarH Q F 0=1:=by simp [polarH,dips_zero h]
lemma polar_green (Q: Matrix U U ℝ)(h:MGreen F):MGreen (polarH Q F):=by
    have hv:MGreen (Dips Q F) := MGreen.times (MG_const _) (h.sub (MG_const _))
    exact MGreen.plus (MGreen.plus (MG_const _) (hv.μ _)) ((hv.times hv).μ _)
-- binomial identity for NONCOMM ring element. avoid coercion collisions by smul
lemma hibernates (Q:Matrix U U ℝ):
    (1 + (-1/2:ℝ)•Q+(3/8:ℝ) •(Q*Q))*(1+Q)*(1 + (-1/2:ℝ)•Q+(3/8:ℝ) •(Q*Q)) - 1 = (Q*Q*Q)*( (5/8:ℝ) • 1 + (-15/64:ℝ) • Q+(9/64:ℝ) •(Q*Q)):=by
        -- noncomm_ring uses casts nsmul not RAT. manual
        simp only [mul_add,add_mul,one_mul,mul_one,smul_mul_assoc,mul_smul_comm,Matrix.mul_assoc]; ext1 i j; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
lemma polar_image (F:Lawn V→Matrix U U ℝ)(Q: Matrix U U ℝ)(h:MGreen F)(f:F 0=Q)(hs:∀ᶠ x in 𝓝 0,(F x).transpose=F x)(hk:IsUnit Q.det):
    ∀ i j,Equal 3 (jPrint (fun x=>(polarH Q F x).transpose*F x*(polarH Q F x)) i j) (jPrint (fun _:Lawn V=>Q) i j):=by
    let M:=Dips Q F; let X:=polarH Q F
    have he (i j): Dark 1 ((jPrint M) i j):=by intro n h'; interval_cases n; rw [coeff_zero_eq_constantCoeff_apply,map_zero]; change constantCoeff (jet _) = _; rw [jet_lead, show M 0=0 from dips_zero f]; simp
    have hx : Q.transpose=Q:= f ▸ hs.self_of_nhds
    let W (x:Lawn V) : Matrix U U ℝ:= ((5/8:ℝ) • (1:Matrix U U ℝ) + (-15/64:ℝ) • (M x))+(9/64:ℝ) •(M x*M x)
    have hS : ∀ᶠ x:Lawn V in 𝓝 0, ((X x).transpose*F x*X x-Q)= Q*(M x*M x*M x)*W x := by
       filter_upwards [hs] with x hx'
       have hb:Q*(1+M x)=F x:= by unfold M Dips; rw [mul_add,mul_one,← Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hk,one_mul]; abel
       have hM:(M x).transpose*Q=Q*M x:= by unfold M Dips; rw [Matrix.transpose_mul,transpose_sub,transpose_nonsing_inv,hx,hx',← Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hk,Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hk,mul_one,one_mul]
       have hZ:(X x).transpose*Q=Q*X x:=by
           have hr:(M x*M x).transpose*Q=Q*(M x*M x):=by rw [Matrix.transpose_mul,Matrix.mul_assoc,hM, ← Matrix.mul_assoc,hM,Matrix.mul_assoc]
           change (1 + (-1/2:ℝ) • M x+(3/8:ℝ) • (M x*M x)).transpose*Q=Q*(1+(-1/2:ℝ) • M x+(3/8:ℝ) • (M x*M x)); simp_rw [transpose_add,transpose_smul, add_mul,smul_mul_assoc,mul_add,mul_smul_comm,hM,hr,transpose_one,mul_one,one_mul]
       conv_lhs=> rw [← hb,←Matrix.mul_assoc,hZ,Matrix.mul_assoc,Matrix.mul_assoc]
       rw [Matrix.mul_assoc Q (M x*M x*M x), show M x*M x*M x * W x=X x*(1+M x)*X x-1 from (hibernates (M x)).symm, mul_sub,mul_one, Matrix.mul_assoc (X x)]
    have hz:MGreen M:= (MG_const _).times (h.sub (MG_const _))
    have hw:MGreen X:=polar_green Q h
    have hh : MGreen W:= MGreen.plus (MGreen.plus ((MG_const _).μ _) (hz.μ _)) ((hz.times hz).μ _)

    let P x:=(X x).transpose*F x*X x; let T:Lawn V→Matrix U U ℝ:=fun x=>Q*(M x*M x*M x)*W x
    have hP:MGreen P:= ((hw.flip.times h).times hw)
    have ht : jPrint P-jPrint (fun _:Lawn V=>Q) = jPrint T:=by rw [← jSub hP (MG_const Q)]; ext1 i j; exact jet_congr (hS.mono fun x p=> show P x i j-Q i j=T x i j from congr_fun (congr_arg (fun M:Matrix U U ℝ => M i) p) j)
    have H {Q R:Matrix U U (Ink V)}{k y:ℕ} (a:∀ i j,Dark k (Q i j))(b:∀ i j,Dark y (R i j)):∀ i j, Dark (k+y) ((Q*R) i j):=by
        intro i j n e; change coeff n (∑ l,Q i l* R l j)=_; rw [map_sum,map_zero]; exact Finset.sum_eq_zero fun l _=>((a i l).eclipse (b l j)).off e
    have hv: jPrint T= jPrint (fun _:Lawn V=>Q)*(jPrint M*jPrint M*jPrint M)*jPrint W:=by
       have he:=(hz.times hz).times hz
       rw [show jPrint T=_ from jTimes ((MG_const Q).times he) hh,jTimes (MG_const Q) he,jTimes (hz.times hz) hz,jTimes hz hz]
    intro i j n e; rw [show jPrint (fun x=> (polarH Q F x).transpose*F x*polarH Q F x) = jPrint T+jPrint (fun _:Lawn V=>Q) from sub_eq_iff_eq_add.mp ht,Matrix.add_apply, map_add, hv, (H (H (k:=0) (fun _ _ i p=>by omega) (H (H he he) he)) (y:=0) (fun _ _ i p=>by omega) i j).off e,zero_add]

omit [Fintype V] in
private lemma silent_exp {n:ℕ}{f g:Ink V}(hf:constantCoeff f=0)(hg:constantCoeff g=0)(p:Equal n (raiseE f) (raiseE g)) : Equal n f g:=by
    let H:=f-g
    have hz:constantCoeff H=0:=by simp [H,hf,hg]
    have ht: Equal n (raiseE H) 1:=by
        have he:g+H=f:=by unfold H; abel
        have hx:Dark n (raiseE g * (raiseE H-1)):=by rw [mul_sub,mul_one,← raise_add hg hz,he]; exact scotch p
        have hb:=hx.times (raise_unit hg); intro i h; apply sub_eq_zero.mp; rw [← map_sub]; exact hb.off h
    have hh:Dark n H:=by
       have hb: Dark n (raiseE H-1):=scotch ht
       intro i hi; cases i with
       | zero=> rw [coeff_zero_eq_constantCoeff_apply,hz,map_zero]
       | succ i=>
          let d:= derivative (POL V); have he:Dark (i+1) (d H):=by
             apply Dark.times (raise_unit hz); rw [← raise_change hz]; intro j hj; rw [coeff_derivative, ht (j+1) (by omega)]; simp
          have he:= he.off (i:=i) (by omega); rw [show d=_ from rfl,coeff_derivative] at he; rw [show coeff (i+1) H=0 from (mul_eq_zero.mp he).resolve_right (by rw [← Nat.cast_add_one]; exact Nat.cast_ne_zero.mpr (by positivity)),map_zero]
    intro i h; apply sub_eq_zero.mp; rw [← map_sub]; exact hh.off h

lemma silentLog {f g:Lawn V→ℝ}{n:ℕ}(he:0<f 0)(h:f 0=g 0)(p:Green f)(q:Green g)(u: Equal n (jet f) (jet g)): Equal n (jet (Real.log ∘ f)) (jet (Real.log ∘ g)) :=by
   let a:= f 0
   have hh {f: Lawn V→ℝ}(v:f 0=a)(p:Green f) : let X:=Real.log ∘ f - fun _=> Real.log a
      constantCoeff (jet X)=0 ∧ jet X=jet (Real.log ∘ f)-realS (Real.log a) ∧ raiseE (jet X)=(realS (a⁻¹))*(jet f):=by
       have ha:0<a:=he; have hp:f 0≠0:=v ▸ ha.ne'
       intro x; have ht: x 0=0:=by simp [x,v]
       have hz:Green (Real.log ∘ f):=p.log hp
       have he:= (show Green x from hz.sub contDiffAt_const)
       refine ⟨by rw [jet_lead, ht, map_zero],by rw [jet_sub (f:=Real.log ∘ f) hz (g:=fun (_:Lawn V)=> _) contDiffAt_const]; exact congr_arg (jet (Real.log ∘ f)-·) (jet_const (U:=V) _),?_⟩
       rw [←literal_exp he ht];
       let g (t:Lawn V):ℝ:= a⁻¹
       rw [show realS _=jet g from (jet_const (U:=V) _).symm,←jet_mul (show Green g from contDiffAt_const) p]
       apply jet_congr; filter_upwards [p.continuousAt.eventually (lt_mem_nhds (by rwa [v]))] with i hi
       simp only [x,Function.comp_apply,Pi.mul_apply,g,Pi.sub_apply, Real.exp_sub, Real.exp_log hi,Real.exp_log ha]; ring
   obtain ⟨x,y,z⟩:=hh (v:=show f 0=a from rfl) p
   obtain ⟨X,Y,Z⟩:=hh (v:=show g 0=a from h.symm) q
   rw [y] at x z; rw [Y] at X Z
   have hx:= silent_exp (n:=n) x X (by rw [z,Z]; exact (Equal.refl _ _).mul u); intro i v; specialize hx i v; simp only [map_sub] at hx; simpa using hx

/-- whitened-network determinant jets including the coarse-reading constant -/
theorem shareD (F:Lawn V→Matrix U U ℝ)(Q: Matrix U U ℝ)(h:MGreen F)(f:F 0=Q)(hs:∀ᶠ x in 𝓝 0,(F x).transpose=F x) (p:0<Q.det) :
    Equal 3 (jet (fun x=>Real.log (polarH Q F x).det)) (jet (fun x=> -1/2*(Real.log (F x).det-Real.log Q.det))):=by
    have hk:IsUnit Q.det:=p.ne'.isUnit
    let X:=polarH Q F; let a (x:Lawn V):=Real.log (X x).det; let b (x:Lawn V):=Real.log (F x).det; let P:=fun x:Lawn V=>(X x).transpose*F x *X x
    have ht:X 0=1:=polar_one f
    have hh : P 0=Q:=by simp [P,ht,f]
    have hy: MGreen X:=polar_green Q h; have hx:MGreen P:= ((hy.flip.times h).times hy)
    have hm: 0<(P 0).det:= by rw [hh]; exact p
    have hf:0<(F 0).det:=f ▸ p
    have hg:0 < (X 0).det:=by rw [ht,det_one]; simp
    have hr:Green a:=hy.det.log hg.ne'; have hq:Green b:=h.det.log hf.ne'
    have hE:= Equal.conic _ _ (polar_image F Q h f hs hk)
    change Equal 3 (jPrint P).det (jPrint (fun _ : Lawn V => Q)).det at hE
    rw [← jDets hx,← jDets (F:=fun _:Lawn V=>Q) (MG_const Q)] at hE
    have hw:= silentLog (f:=fun x=>(P x).det) hm (g:=fun _=> Q.det) (by rw [hh]) hx.det contDiffAt_const hE
    have hv: jet (fun x=>Real.log (P x).det)=jet a+jet b+jet a:=by
        rw [← jet_add hr hq,← jet_add (show Green (a+b) from hr.add hq) hr]; apply jet_congr
        filter_upwards [hy.det.continuousAt.eventually (lt_mem_nhds hg),h.det.continuousAt.eventually (lt_mem_nhds hf)] with x hv h' using by dsimp [P,b,a]; simp only [Matrix.det_mul,Matrix.det_transpose,Real.log_mul (mul_ne_zero hv.ne' h'.ne') hv.ne', Real.log_mul hv.ne' h'.ne']
    change Equal 3 (jet (fun x=>Real.log (P x).det)) (jet (fun _=>Real.log Q.det)) at hw
    rw [hv,jet_const] at hw
    let c (x:Lawn V):ℝ:= Real.log Q.det; let v:= jet (U:=V) c; have he:v=realS (U:=V) (Real.log Q.det):= jet_const _
    change Equal 3 (jet a) (jet ((fun x:Lawn V=> (-1/2:ℝ))*(b-c)))
    rw [jet_mul (f:=fun _:Lawn V=>(-1/2:ℝ)) (g:=b-c) contDiffAt_const (by exact hq.sub contDiffAt_const),jet_const,jet_sub hq (g:=c) contDiffAt_const, show jet c=realS _ from he];
    intro i t; specialize hw i t; simp only [map_add] at hw; rw [← real_alg, ← Algebra.smul_def, coeff_smul, map_sub, ← hw]; simp; module
end pads
end YM.WilsonCoeffUV.Blue.Cameo
