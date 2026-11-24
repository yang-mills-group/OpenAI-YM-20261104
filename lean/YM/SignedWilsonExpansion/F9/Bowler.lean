import YM.SignedWilsonExpansion.F9.Intaglio
/-!
# The non-redundant top equations really disappear on the epoch (when isolated)

No Ward assumption on the course from top epoch down or on the physical
regulator! Prove using both retained links and moving mirror colors, not
copying the odd convention, with spectators not touched in either half.
Contacts evaluated in genuine **even** period geometry. `IBP_solo`.
-/
set_option autoImplicit false
set_option maxHeartbeats 810000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa.StationA
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Matrix
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost FVA2
open Cloth XSpace
open PertExtension PertExtension.Orb FormalOPE FormalOPE.RG10 FormalOPE.RG10.InversionWard
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical ENNReal InnerProductSpace
variable {G:Gauge}{H:Hol G}{h i j k m r d n l:ℕ}{F:Frame G h}{x:Label G h}{P:Period} {s:Side} {ι:Type*}
section contact
variable {S:Finset Cover}(R:Rays G h H)(M:Tensor.T (Snap G h) ℂ (r+1))(f:R.FitsAt S)(p:Rays.covariantTensor M)
    {v:Config G s→ℝ}{b:Set (Site s)}(x:Site s)(hv:Proxy v)(q:LocalOn b v) (he:FitsIn S s)(room:∀ a:R.edg, avoids (edgeAt a.val x) (footprint S x))
    (clear:∀ a:R.edg, off (edgeAt a.val x) b)
def paint (a:R.edg)(U:Config G s): G.Color:= (InnerProductSpace.toDual ℝ G.Color).symm (Complex.reCLM.comp (places x (R.coField M a) U))
lemma paint_eq (a:R.edg)(U:Config G s)(A:G.Color): ⟪paint R M x a U,A⟫_ℝ=Complex.re (R.coField M a (expandAt x U) A):= InnerProductSpace.toDual_symm_apply
lemma paint_proxy (a:R.edg): Proxy (paint R M x a):=by
    let P:Config G s→ G.Color:=paint R M x a; let X(i:G.ColorIndex):= fun U=> ⟪paint R M x a U,dirs G i⟫_ℝ • dirs G i
    have h: P= ∑ i,X i:=by
        funext U; rw [Finset.sum_apply]; refine ((dirs G).sum_repr (P U)).symm.trans ?_; exact Finset.sum_congr rfl fun i _=> by rw [OrthonormalBasis.repr_apply_apply]; apply congr_arg (· • dirs G i); exact real_inner_comm ..
    change Proxy P; rw [h]; refine Proxy.sum _ fun i _=>?_; unfold X; simp_rw [paint_eq]; exact ((proxy x (Maskable.color_coField_at R M a (dirs G i))).after _ Complex.reCLM.contDiff).after (fun k : ℝ=> k • dirs G i) (contDiff_id.smul contDiff_const)
include f in
lemma paint_read (a:R.edg): LocalOn (footprint S x) (paint R M x a):=by
    have v:= (R.coField_affordable f M a).uses; have ht: LocalOn (footprint S x) (places x (R.coField M a)):=by simpa only [footprint,places, Finset.coe_image] using! LocalOn.expandAt ↑S (R.coField M a) v x
    exact fun U V t=> congr_arg (fun w:Covector G=> (InnerProductSpace.toDual ℝ G.Color).symm (Complex.reCLM.comp w)) (ht U V t)
private lemma effort_here (e:Even s.val)(U:Config G s)(he:retained U) (a:R.edg): InversionWard.effort (edgeAt a.val x) (paint R M x a) U= Complex.re (places x (fun V=> R.coField M a V (WardBin.euler V a.val)) U):= by
    unfold places; dsimp only [Function.comp_apply]; rw [InversionWard.agrees e _ _ he,paint_eq]; exact congr_arg (fun y:G.Color => Complex.re (R.coField M a (expandAt x U) y)) (Eq.symm (euler_at ..))
lemma effort_color (e:Even s.val)(U:Config G s)(he:retained U) : places x (Pill.holder R M p).f U=∑ i:R.edg, effort (edgeAt i.val x) (paint R M x i) U:=by
    change Complex.re (R.force M (expandAt x U))=_; rw [R.force_eq, Complex.re_sum]; exact Finset.sum_congr rfl fun i _=> (effort_here R M x e U he i).symm
include f he room in
private theorem atFall (j:R.edg)(U:Config G s) : fallout (edgeAt j.val x) (paint R M x j) U= Complex.re (WardBin.divergence j.val (R.coField M j) (expandAt x U)):=by
    let a:= edgeAt j.val x; let g(t:G.Color):CoverConfig G→ℂ:= fun y=> R.coField M j y t; let h:(CoverConfig G)→Covector G:=R.coField M j; let X:=paint R M x j
    have hp:= R.coField_affordable f M j
    rw [singlyDiv a (paint_read R M f x j) (room j) (paint_proxy R M x j), WardBin.divergence,Complex.re_sum]; apply Finset.sum_congr rfl; intro i _
    let v:=dirs G i; let F(y:Config G s):=h (expandAt x y) v
    have hx(a): ⟪v,paint R M x j a⟫_ℝ=Complex.re (F a):=(real_inner_comm ..).trans (paint_eq R M x j a v)
    have ht:= hp.postcomp (ContinuousLinearMap.apply ℝ ℂ v); have hy:F=places x (g v):=rfl
    change WardBin.slope a v (fun u'=> ⟪v,paint R M x j u'⟫_ℝ) U=_; simp_rw [hx];
    have hLocal: LocalOn (footprint S x) F:=by rw [hy]; simpa only [footprint,places, Finset.coe_image] using! LocalOn.expandAt ↑S (g v) ht.uses x
    have eq':WardBin.slope j.val v (g v) (expandAt x U)= WardBin.slope a v F U:=(congr_fun (slopes_at ht.uses he x (R.fitsAt_edge f j).1 v) U).symm; change _=Complex.re (WardBin.slope j.val v (g v) (expandAt x U)); rw [eq']; change WardBin.slope a v (Complex.reCLM ∘ F) U= Complex.re (WardBin.slope a v F U); unfold WardBin.slope
    have hD: (fun t:ℝ=> F (slide a U (t • v)))= fun t=>F (tilt a U (t • v)):= funext (fun t=>(tilt_isolated a hLocal (room j) (t • v) U).symm)
    have hz: HasDerivAt (fun t:ℝ=>F (slide a U (t • v))) (vary a F U v) 0:= by rw [hD]; exact InversionWard.Proxy.derivative a (proxy x (Maskable.color_coField_at R M j v)) U v
    rw [hz.deriv]; exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hz).deriv

include f he room in
lemma compress_color (U:Config G s): places x (Pill.sink R M p).f U=∑ i:R.edg, fallout (edgeAt i.val x) (paint R M x i) U:=by change Complex.re (R.compression M (expandAt x U))=_; rw [Rays.compression,Complex.re_sum]; exact Finset.sum_congr rfl fun i _=>(atFall R M f x he room i U).symm

include f hv q he room clear
theorem measureWard (e:Even s.val) (t:ℝ)(ht:t≠0):
    preExpectation (places x (Pill.holder R M p).f*v) t=t^2*preExpectation (places x (Pill.sink R M p).f*v) t :=by
    let S(a:R.edg):=effort (edgeAt a.val x) (paint R M x a) * v; let X(a:R.edg):= fallout (edgeAt a.val x) (paint R M x a)*v
    have he (U:Config G s)(w:retained U): (places x (Pill.holder R M p).f*v) U= (∑ a,S a) U:=by unfold S; rw [Finset.sum_apply,Pi.mul_apply,effort_color R M p x e U w,Finset.sum_mul]; rfl
    have hx : places x (Pill.sink R M p).f * v=∑ a,X a:= by funext U; unfold X; rw [Finset.sum_apply,Pi.mul_apply,compress_color R M f p x ‹FitsIn _ _› room U, Finset.sum_mul]; rfl
    have hab : preExpectation (places x (Pill.holder R M p).f*v) t= preExpectation (∑ a,S a) t:=by unfold preExpectation; congr 1; unfold preNum; apply MeasureTheory.integral_congr_ae; exact Eventually.of_forall (fun i=> congr_arg (fun x=> x * _) (he _ (mirrors e i)))
    rw [hx,hab, expectation_sum Finset.univ S (fun i _=> ((paint_proxy R M x i).effort _).mul hv), expectation_sum Finset.univ X (fun i _=> ((paint_proxy R M x i).fallout _).mul hv), Finset.sum_apply, Finset.sum_apply,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    have hp:= orbit_IBP e (edgeAt i.val x) (paint_proxy R M x i) ht hv; rw [isolated (edgeAt i.val x) q (clear i), show preExpectation (0:Config G s→ℝ) t=0 from ?_,add_zero] at hp; exact hp; simp [preExpectation,preNum]
omit f hv q he room clear
end contact
lemma payment {Q:Config G s→ℝ}(u:Even s.val){V:Config G s→ℝ}(p:PreTest Q)(v:PreTest V)
    (p':∀ t, t≠0 →preExpectation Q t=t^2*preExpectation V t): replyCoeff Q=X^2*replyCoeff V:=by
   unfold replyCoeff; have hX:InversionTop.into X=X:=map_X _
   let Y:=fun i:ℕ=> if i=2 then (1:ℝ) else 0; have h : PertExtension.Series.Tested.Aspiration (fun x:ℝ=>x^2) Y:=by simpa [Y] using! PertExtension.Series.Tested.Aspiration.single (1:ℝ) 2
   have he := unique_wilson (PertExtension.Series.Tested.eventually_pos.mono (fun x hx=> p' x hx.ne')) (before_tree_formula u (traySpec G) p) (h.prod (before_tree_formula u (traySpec G) v)) -- replace
   have hp : PowerSeries.mk Y=X^2:= by apply PowerSeries.ext; intro n; rw [PowerSeries.coeff_mk,coeff_X_pow]
   have hx : PowerSeries.mk (Orb.diag (restrictedO Q))= X^2*PowerSeries.mk (Orb.diag (restrictedO V)):= by apply PowerSeries.ext; intro i; rw [←hp,PowerSeries.coeff_mk]; exact congr_fun he i
   rw [hx,map_mul,map_pow,hX]

section kappa
variable {S:Finset Cover}(R:Rays G h H)(M:Tensor.T (Snap G h) ℂ (r+1))(T:P.Tree)(x:Site P.side)
lemma sameBook {f:Config G P.side→ℝ}(p:PreTest f): XSpace.Bare.normalized T G (BareOrb.stencil T f)= replyCoeff f:=BareOrb.diagram_eq T p
lemma tunic (i:ℕ)(X:Bare.Series T G):Bare.normalized T G (_root_.PowerSeries.X^i*X)=_root_.PowerSeries.X^i*Bare.normalized T G X:=by conv_lhs=> rw [show _root_.PowerSeries.X^i*X=Bare.scalar _ _*X from congr_arg (fun Y=>Y*X) (show PowerSeries.X^i = XSpace.Bare.scalar T (G:=G) (PowerSeries.X^i) from (by simp [Bare.scalar]))]; exact Bare.normalized_scalar T _ X
lemma mergeBook {f g:Config G P.side→ℝ} (p:ContDiff ℝ ω (f∘T.links))(v:ContDiff ℝ ω (g∘ T.links)): BareOrb.stencil T (f*g)=BareOrb.stencil T f*BareOrb.stencil T g:=by
    unfold BareOrb.stencil TreeFormal.enter; refine Eq.trans (congr_arg (XSpace.Taylor.expandTaylor (T.basis G)) ?_) (XSpace.Taylor.expand_mul _ (attendance T p) (attendance T v)); funext U; exact Complex.ofReal_mul ..
namespace Terms
theorem drop {p':Rays.covariantTensor M}(f:R.FitsAt S)(room:∀ a:R.edg, avoids (edgeAt a.val x) (footprint S x))
    {b:Set (Site P.side)}(he:FitsIn S P.side)(clear:∀ a:R.edg, off (edgeAt a.val x) b)
    {Q:Config G P.side→ℝ}{Y:Bare.Series T G}(hx:LocalOn b Q)(p:Proxy Q)(z:PreTest Q)(u:ContDiff ℝ ω (Q ∘ T.links))(hz:X^i * Y=BareOrb.stencil T Q):
    Bare.normalized T G (propose T x (Pill.holder R M p') * Y)= Bare.normalized T G (X^(Pill.shadeShift r)*propose T x (Pill.sink R M p') * Y):=by
    let U:=Pill.holder R M p'; let V:=Pill.sink R M p'; let a:=places x U.f; let v:= places x V.f; let h:=InversionTop.Uses.pre_mul (candle U x) z; let y:=InversionTop.Uses.pre_mul (candle V x) z; let e:= even_iff_two_dvd.mpr P.even
    have he':Bare.normalized T G (X^U.rank*propose T x U*(X^i*Y)) = X^2*Bare.normalized T G (X^V.rank*propose T x V*(X^i*Y)):=by
        rw [hz,apex,apex, ←mergeBook T (flies _ U.valid _) u,←mergeBook T (flies _ V.valid _) u, sameBook T h,sameBook T y]; exact payment e h y (measureWard R M f p' x p hx he room clear e)
    apply mul_left_cancel₀ (a:=PowerSeries.X^(U.rank+i)) (pow_ne_zero _ X_ne_zero); rw [← tunic,← tunic]
    let A:= propose T x U; let B:=propose T x V; change Bare.normalized T G (X^(U.rank+i)*(A*Y))= Bare.normalized T G (X^(U.rank+i)*(X^Pill.shadeShift r*B*Y)); rw [show (PowerSeries.X^(U.rank+i)*(A*Y))=X^U.rank*A*(X^i*Y) by rw [pow_add];ring,show (PowerSeries.X^(U.rank+i)*(X^Pill.shadeShift r*B*Y))=X^2*(X^V.rank*B*(X^i*Y)) from ?_,tunic]; exact he'; have hY : U.rank+Pill.shadeShift r=V.rank+2:=Pill.shade_sense
    calc _ = X^(U.rank+Pill.shadeShift r)*B*(X^i*Y):= by rw [pow_add,pow_add];ring
         _=_:=by rw [hY,pow_add];ring
end Terms
end kappa
end YM.WilsonCoeffUV.Mer.Xa.StationA
