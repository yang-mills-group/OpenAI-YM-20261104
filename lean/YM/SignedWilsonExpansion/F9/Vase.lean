import YM.SignedWilsonExpansion.F9.Glass
import YM.SignedWilsonExpansion.F9.Motion
/-!
# Exact WCU Mer point stencil for compact analytic witnesses
Uses *all* periods, finite matrix footprint, lift to the cover, inverse link
slope and endpoint derivatives will be literal at the retained power even on
folded histories. Does not use a canonically repriced compensated coupling at
top; this is a raw divided Taylor. Based on Root.Step's on-lattice section
argument using local matrix cost only for these additional pillars.
-/
set_option autoImplicit false
set_option maxHeartbeats 740000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa.Pill
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Matrix
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical ENNReal
variable {n:Side}{h d i k r e:ℕ}{G:Gauge}(P:Pill G)

abbrev territory:= P.valid.choose
def prism := P.valid.choose_spec.choose
lemma at_prism (U:CoverConfig G): P.f U=P.prism (body U P.territory):= P.valid.choose_spec.choose_spec.2 U
lemma prism_hot : ContDiff ℝ ω P.prism:= P.valid.choose_spec.choose_spec.1
abbrev tag := ↥P.territory × G.ColorIndex
def site (i:P.tag):YForest G:= stone i.1.val i.2
def color (x:Lawn P.tag)(i:P.territory) := coatC G fun j=> x (i,j)
lemma site_inj : Injective P.site:= by
    rintro ⟨⟨p,hp⟩,i⟩ ⟨⟨q,hq⟩,j⟩ x; apply Prod.ext; · apply Subtype.ext; exact (feather_at _ _).symm.trans ((congr_arg feather x).trans (feather_at ..))
    exact congr_arg (fun v:YForest G=> v.2.2) x
def arena (x:Lawn P.tag): ℝ:= P.prism (fun i=> G.mat (G.lieExp (P.color x i)))
def clears (x:Lawn P.tag): Fabrication G:=fun i=>if hx:i∈ P.territory then P.color x ⟨i,hx⟩ else 0
lemma at_gate (x:Lawn P.tag)(t:ℝ) : arena P (t • x)= P.f (roof (clears P x) t):= by rw [P.at_prism]; apply congr_arg (prism P); funext i; unfold body roof clears; rw [dif_pos i.property]; rfl
lemma hot : Green P.arena:= (P.prism_hot.comp (contDiff_pi.mpr fun i=> G.exp_jet.comp ((coatC G).toContinuousLinearMap.contDiff.comp (contDiff_pi.mpr fun i=>contDiff_apply ..)))).contDiffAt
lemma jet_r (q:i<P.rank): coeff i (jet P.arena)=0:=by
    apply MvPolynomial.funext; intro x; rw [rayon]; obtain ⟨C,hc,v⟩:= P.bound (clears P x); let V:ℝ→L[ℝ] Lawn P.tag:=(ContinuousLinearMap.id ℝ ℝ).smulRight x; rw [map_zero]; change Tensor.diagonal (Tensor.coeff P.arena i 0) x=0; rw [← WardBin.leading_tensor x _ (P.hot.of_le le_top)]; exact ray_leading (P.arena ∘ V) ((show ContDiffAt ℝ i P.arena (V 0) from by rw [map_zero]; exact P.hot.of_le le_top).comp _ V.contDiff.contDiffAt) q C (v.mono fun t h=>by change ‖P.arena (t • x)‖≤_; rw [P.at_gate]; exact h)

def letter: Era G ℝ:= (
    fun n e=> Blue.fade (spear (foldUnder n ∘ P.site)) (sprig P.arena P.rank e),
    fun e=> Blue.fade (spear P.site) (sprig P.arena P.rank e))
lemma facet (X:Lawn (Woods G n)) : P.f (expandAt 0 (mantle X))= P.arena (spear (foldUnder n∘ P.site)*ᵥ X):=by
    rw [P.at_prism,arena]; apply congr_arg (P.prism); funext i; unfold body expandAt; rw [bare_linkC,spear_act,add_zero]; rfl

def reading (n:Side) (x:Lawn (Woods G n)):= P.f (expandAt 0 (mantle x))
lemma nearby (n:Side) : Green (P.reading n):= by rw [show P.reading n=P.arena ∘ (fun x=>spear (foldUnder n ∘ P.site)*ᵥ x) from funext fun x=> P.facet x]; exact (ContDiffAt.comp (g:=P.arena) _ (by rw [Matrix.mulVec_zero]; exact P.hot) (board _))
lemma flare (n:Side): PowerSeries.X^P.rank * flash (P.letter.1 n)= jet (P.reading n):=by
    let W:= spear (foldUnder n∘ P.site); let K:= sprig P.arena P.rank; have he : PowerSeries.X^P.rank* flash K= jet P.arena:= moves P.arena fun i u=> P.jet_r u; have hh:= congr_arg (loom W) he
    rw [map_mul,map_pow,show loom W PowerSeries.X=PowerSeries.X from by simp [loom],loom_jet W P.arena P.hot] at hh
    rw [show P.letter.1 n=(fun i=>Blue.fade W (K i)) from rfl,←loom_fade W K (finite_shell (sprig_count P.arena P.rank))]; exact hh.trans (congr_arg jet (funext (fun v=> (P.facet v).symm)))
private def bendV (s:Signed)(P Q:Pill G)(p: P.rank=Q.rank)(h:∀ U, P.f (pull s 0 U)= Q.f U): Roll s P.letter Q.letter:=by
    intro n X I x A A' hx; have hg: Q.reading n ∘ A =ᶠ[𝓝 0] P.reading n ∘ A':=by
       filter_upwards [hx.shift] with t ht; unfold reading; simp only [Function.comp_apply, ht,expandAt_gauge,expandAt_pull,affine,Signed.act_zero,add_zero]; rw [P.inv,h]
    apply mul_left_cancel₀ (a:=PowerSeries.X^P.rank) (pow_ne_zero _ X_ne_zero)
    have hh (y:Lawn X→ TreeVars G n)(hy:Green y)(h:y 0=0)(T:Pill G) : PowerSeries.X^T.rank*train (spool y) (flash (T.letter.1 n))=jet (T.reading n ∘ y):=by
       conv_lhs=> arg 1; arg 1; rw [←train_X (spool y)]
       rw [← map_pow, ←map_mul, T.flare,traveling y hy h _ (T.nearby n)]
    nth_rw 1 [p]; rw [hh A hx.g₀ hx.f₀ Q,hh A' hx.g₁ hx.f₁ P]; exact jet_congr hg
lemma rolled (s:Signed): Roll s P.letter (P.spins s|>.letter):= bendV s _ _ rfl fun _=> rfl
-- same-sector authentication
private lemma fare (e r:ℕ) : Bends 0 (fun n=> P.letter.1 n e r) (P.letter.2 e r):=by
    let f:=sprig P.arena P.rank e; let d:=P.site; let p n:=foldUnder n∘ d
    let U (n:Side)(b:Fin r→ P.tag) (t:dock (Site n) (Hooks G) r):= if p n ∘ b=t then f r b else 0
    let X (b:Fin r→P.tag)(z:Fin r→ YForest G) := if d ∘ b=z then f r b else 0
    have hx {V:Type}(g:P.tag→V)(t:Fin r→V)[DecidableEq V]: Blue.fade (spear g) f r t= ∑ b:Fin r→P.tag, if g ∘ b=t then f r b else 0:=by
        unfold Blue.fade; apply Finset.sum_congr rfl; intro b _; split
        next h'=> rw [←h']; simp [spear]
        next h'=> obtain ⟨i,hi⟩:=Function.ne_iff.mp h'; rw [Finset.prod_eq_zero (Finset.mem_univ i),zero_smul]; exact if_neg hi.symm
    have hT : P.letter.2 e r=∑ b:Fin r→P.tag,X b:= by ext1 t; rw [Finset.sum_apply]; exact hx d t
    have he b: Bends 0 (fun n=> U n b) (X b):=by
       let A:ℝ:= ‖f r b‖ * Real.exp (port_d 0 (d ∘ b))
       have ha: 0≤A:=mul_nonneg (norm_nonneg _) (by positivity)
       refine ⟨fun y=>tendsto_const_nhds.congr' ?_,1,A,one_pos,(Soil.seen (p:=0) (d ∘ b)).mono fun n hn=>⟨ha,fun i=>?_⟩⟩
       · filter_upwards [eventually_all.mpr (fun i:Fin r=> fold_faith (d (b i)) (y i))] with n hn; have hw : p n ∘ b=slideC n y ↔ d ∘ b=y:= ⟨fun q=>funext fun i=> (hn i).mp (congr_fun q i),fun q=>congr_arg (slideC n) q⟩; unfold X U; simp only [hw]
       unfold U; split
       next h => rw [←h,show tread (tor n) (wrap n 0) (p n ∘ b)= port_d 0 (d ∘ b) from hn,neg_one_mul,Real.exp_neg]; unfold A; rw [mul_assoc,mul_inv_cancel₀ (by positivity),mul_one]
       rw [norm_zero]; exact mul_nonneg ha (by positivity)
    rw [hT]; refine (Bends.sum (s:=Finset.univ) (fun b _=>he b)).congr (Eventually.of_forall fun n=>?_); ext1 t; simp only [Finset.sum_apply]; exact (hx (p n) t).symm
lemma solid : Auth P.rank P.letter := by
    have hp n:shellK P.rank (P.letter.1 n):=fade_shell _ (sprig_count _ _)
    refine ⟨P.fare,hp,fun n i=> fade_pure (sprig_pure P.arena P.hot P.rank i) _, fun n=> certify (ι:=Unit) (fun _=>LinearMap.id) (fun _ _ f=> f ()) _ (hp n) (fun _=>?_) ⟩
    intro Z I x A A' v; exact bendV 1 P P rfl (by simp) n v


-- At its own rank: same powers after crossing arbitrary nonlinear
-- link-jet inserts. Leading tensor uses just linear `grain` reads.
section
variable {X Y:Type*}[Fintype Y][Fintype X]
private lemma Acoeff (x:X→Ink Y)(Q:POL X)(v:Lawn Y) : MvPolynomial.eval v (constantCoeff (MvPolynomial.aeval (R:=ℝ) x Q))= MvPolynomial.eval (fun i=> MvPolynomial.eval v (constantCoeff (x i))) Q:=by
    induction Q using MvPolynomial.induction_on with
    | C a=> rw [MvPolynomial.aeval_C, real_alg]; simp [realS]
    | add r p a b=> simp_rw [map_add,a,b]
    | mul_X r i h=> simp_rw [map_mul,MvPolynomial.aeval_X,MvPolynomial.eval_X,h]
private lemma trained (x:X→Ink Y)(F:Ink X)(p:∀ i<k,coeff i F=0)(v:Lawn Y):
     MvPolynomial.eval v (coeff k (train x F))= MvPolynomial.eval (fun i=> MvPolynomial.eval v (constantCoeff (x i))) (coeff k F):= by
       rw [train,edit_coeff _ _ _ (Nat.lt_succ_self k),map_sum, Finset.sum_eq_single k]; swap; · intro i hi h; rw [p i (by have ht:=Finset.mem_range.mp hi; omega),map_zero,zero_mul,map_zero]
       swap; · simp
       rw [coeff_mul_X_pow',if_pos le_rfl,Nat.sub_self,coeff_zero_eq_constantCoeff_apply]; exact Acoeff ..
private lemma compose1 (g: Lawn X → Lawn Y)(p:Green g)(v:Lawn X)(X0:Lawn Y)(q:∀i,fderiv ℝ (fun a=>g a i) 0 v=X0 i)(f:Lawn Y→ℝ)(he:∀ i<k,coeff i (jet f)=0)(hu:g 0=0)(hv:Green f): Tensor.diagonal (Tensor.coeff (f∘g) k 0) v= Tensor.diagonal (Tensor.coeff f k 0) X0:=by
    have hk: (fun i=>MvPolynomial.eval v (constantCoeff (spool g i)))= X0:=funext fun i=>by rw [← coeff_zero_eq_constantCoeff_apply,spool,coeff_mk,rayon]; change _=X0 i; rw [q i|>.symm]; simp
    rw [show Tensor.diagonal (Tensor.coeff (f∘g) k 0) v= _ from Eq.symm (rayon ..), ← traveling g p hu f hv, trained _ _ he v, hk]; exact rayon ..
end
private lemma stationed (Z: Snap G h) (x: Lawn (Cart G h))(ht:x=casing G h Z)(H: Hol G):
    Tensor.diagonal (Tensor.coeff (P.f ∘ curve H) P.rank 0) Z= Tensor.diagonal (Tensor.coeff P.arena P.rank 0) (fun i=>grain Z (P.site i)):=by
    subst x; let L: Lawn (Cart G h)→L[ℝ] Snap G h:= (casing G h).symm.toContinuousLinearMap; let K:Lawn (Cart G h)→ Lawn P.tag:= fun x i=> flex (P.site i) (L x); let g:= P.f ∘ curve (d:=h) H; let v:= casing G h Z
    have he (X:Snap G h) i: P.color (fun j=>flex (P.site j) X) i= G.plog (G.mat (curve H X i.val)):=by ext1 j; rw [← show Film.lane (Place.seat (i.val.1)) i.val.2 X= G.plog (G.mat (curve H X i.val)) from Film.lane_truth H i.val X]; change flex (stone i.val j) X= _; rw [flex,feather_at]; rfl
    have hb i: Tendsto (fun v:Snap G h=> curve H v i) (𝓝 0) (𝓝 1):=by
       have ht: ContinuousAt (fun v:Snap G h=> curve H v i) 0:=(G.continuous_mat.isClosedEmbedding G.mat_injective).isInducing.continuousAt_iff.2 (WardBin.plot H i h).continuousAt
       simpa only [curve_zero,Pi.one_apply] using (show Tendsto (fun v:Snap G h=>curve H v i) _ (𝓝 (curve (d:=h) H 0 i)) from ht.tendsto)
    have hx : Tendsto L (𝓝 0) (𝓝 0):=by rw [← map_zero L]; exact L.continuous.tendsto _
    have hm : g∘ L=ᶠ[𝓝 0] P.arena ∘ K:=by
       filter_upwards [hx.eventually (eventually_all.mpr (fun i:↥P.territory=> (hb i.val).eventually G.plog_right))] with x u
       change P.f (curve H (L x))= P.prism (fun i=> G.mat (G.lieExp (P.color (K x) i)))
       rw [P.at_prism]; apply congr_arg P.prism; funext i; unfold K; rw [he (L x) i, u i]; rfl
    have hu: ContDiffAt ℝ ω g 0:=by
       have hh: g = fun v:Snap G h=> P.prism (body (curve H v) P.territory):= funext fun _=> P.at_prism _
       rw [hh]; exact P.prism_hot.contDiffAt.comp _ (contDiffAt_pi.mpr fun i=>(Work.G02.linkGerm H h i.val).1.contDiffAt)
    have hy(i: P.tag): ContDiffAt ℝ ω (fun x=> K x i) 0:= (show ContDiffAt ℝ ω (flex (P.site i)) (L 0) from by rw [map_zero]; exact flex_smooth (P.site i)).comp (0:Lawn (Cart G h)) L.contDiff.contDiffAt
    have hψ (i: P.tag): fderiv ℝ (fun x=> K x i) 0 v =grain Z (P.site i):=by
       change fderiv ℝ (flex (P.site i) ∘ L) 0 v= _; have hp: DifferentiableAt ℝ (flex (P.site i)) (L 0):= by rw [map_zero]; exact (flex_smooth _).differentiableAt (by simp)
       rw [fderiv_comp (𝕜:=ℝ) 0 hp L.differentiableAt,ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply,map_zero, show L v=Z from (casing G h).symm_apply_apply Z,grace]
    have hg:= compose1 K (contDiffAt_pi.mpr hy) v _ hψ P.arena (fun i h=>P.jet_r h) (funext fun i=>by unfold K; rw [map_zero,flex_zero]; rfl) P.hot
    change Tensor.diagonal (Tensor.coeff g P.rank 0) Z= _
    rw [← hg,Tensor.diagonal,Tensor.diagonal,Tensor.coeff, Tensor.coeff,((hm.iteratedFDeriv ℝ P.rank).eq_of_nhds).symm] -- inspect library
    rw [Next.Foundations.jets_linear L (hu.of_le le_top)]; simp only [_root_.smul_apply,ContinuousMultilinearMap.compContinuousLinearMap_apply]; rw [show L v=Z from (casing G h).symm_apply_apply Z]; rfl

private lemma stamp (u:Fin P.rank→P.tag): P.letter.2 0 P.rank (P.site ∘ u)=rye P.arena P.rank u:=by
   simp only [letter, Blue.fade]; rw [Finset.sum_eq_single u]; swap; · intro i hi h; obtain ⟨v,hv⟩:= Function.ne_iff.mp h; rw [Finset.prod_eq_zero (Finset.mem_univ v),zero_smul]; rw [spear,Matrix.of_apply]; exact if_neg (fun h=>hv ((P.site_inj h).symm))
   swap; · simp
   simp [spear,sprig,shine_lit]
private lemma excise (x:Fin P.rank→ YForest G)(v:x∉Set.range (fun u=> P.site ∘ u)): P.letter.2 0 P.rank x=0:= by
    unfold letter; refine Finset.sum_eq_zero (fun i _=>?_); obtain ⟨p,hp⟩:= Function.ne_iff.mp (show P.site ∘ i≠x from fun t=> v ⟨_,t⟩); rw [Finset.prod_eq_zero (Finset.mem_univ p),zero_smul]; exact if_neg hp.symm
lemma home (H:Hol G)(J:Jet G)(t:ℝ)(h:ℕ): Fountain.vein (vitre h (P.letter.2 0 P.rank)) J t= Tensor.diagonal (Tensor.coeff (P.f ∘ curve H) P.rank 0) (engineered t (trunk h J)):=by
    let x:= engineered t (trunk h J); let F (v:Fin P.rank→ P.tag):= P.site ∘ v; rw [vineyard _ _ _ P.solid]; rw [tsum_eq_sum (s:= Finset.univ.image F), Finset.sum_image ((show Injective F from fun p q h=>funext fun t=> P.site_inj (congr_fun h t)).injOn)]; swap; · intro u hu; rw [P.excise u (fun ⟨v,h⟩=> hu (Finset.mem_image.mpr ⟨_,Finset.mem_univ v,h⟩)),zero_mul]
    rw [P.stationed x _ rfl H, show Tensor.diagonal (Tensor.coeff P.arena _ 0) (fun i=> _)=_ from Eq.symm (rayon P.arena P.rank (fun i=> grain x (P.site i))),jet_apply,toll]; exact Finset.sum_congr rfl fun i _=> by rw [P.stamp]; rfl
lemma principal_tile (H:Hol G)(J:Jet G)(d n:ℕ): (Labels.read J) (seedTile (vitre d (P.letter.2 0 P.rank)) n) = (WardBin.leading n (fun t=> Tensor.diagonal (Tensor.coeff (P.f ∘ curve H) P.rank 0) (engineered t (trunk d J))):ℝ):=by rw [reads_seedTile, funext fun v=> P.home H J v d]
end YM.WilsonCoeffUV.Mer.Xa.Pill
