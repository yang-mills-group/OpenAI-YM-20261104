import YM.OPE.Compatible.Grafts.Lack
/-!
# Ordinary and quotient paths. Poles
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}
variable (S:StepData c f)(he:Odd S.ratio.count.val)
local notation "X!"=> forest S.ratio he
local notation "Z!" => AxisChart G X!
local notation "K!" => Bid.Dir G c
local notation "U!" => Bid.Dir G f
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass Coin Pilot Radial Flock
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v}{D:Alps K T d u} (U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:licensed S he U A.clip A.live L A.sky g)
variable {P:ChartRatio G}(ht:LocalRatio P)
local notation "Pz"=>pane X! t A.clip A.live
abbrev OreA {G:Gauge}{V:ℝ}{K:Sponsor G}{T:Seasons K}(A:Alps K T i V)(b:ℝ)(w:Bid.Dir G c × AxisChart G (forest S.ratio he)):= Real.exp ((-b)*pane X! t A.clip A.live w -springF X! A.live w.2)
-- Hessian Lamp
abbrev office (D:Law Z!):Prop:=∀ (x y:Z!), D.P x y= dotProduct (cash (countingBasis X! G) x) (FUND S he U *ᵥ cash (countingBasis X! G) y)
include h t
lemma pegZ (hs:G.Simple): fderiv ℝ Pz 0=0:=by
     let D:= fderiv ℝ Pz 0; have hh(v:G.El)(x:K!× Z!): D (Busk S he v x)= D x:=by
          have hp:= stillZ S he U t h v 1 ![x]; rw [show Busk S he v ∘ ![x]=![Busk S he v x] from funext fun i=>by fin_cases i; rfl, iteratedFDeriv_one_apply,iteratedFDeriv_one_apply] at hp; exact hp
     let LX:=ContinuousLinearMap.inl ℝ K! Z!; let LY:= ContinuousLinearMap.inr ℝ K! Z!; have hY(v:G.El)(x:K!): D (LX (glint (Body 1 c) v x))=D (LX x):= (show Busk S he v (LX x)=LX (glint (Body 1 c) v x) from Prod.ext rfl (show glint (forest S.ratio he).Free v 0=0 from map_zero _)) ▸ hh v _ -- implicit RHS
     have hv(v:G.El)(x:Z!): D (LY (glint _ v x))=D (LY x):=(show Busk S he v (LY x)= LY (glint (forest S.ratio he).Free v x) from Prod.ext (show glint (Body 1 c) v 0=0 from map_zero _) rfl) ▸ hh v _
     apply ContinuousLinearMap.ext; rintro ⟨x,y⟩; change D (x,y)=0; rw [show (x,y)=LX x+LY y from Prod.ext (add_zero _).symm (zero_add _).symm,map_add,show D (LX x)=0 from YM.Stationary.slot_fixed hs (D ∘L LX) hY x,show D (LY y)=0 from YM.Stationary.slot_fixed hs (D ∘L LY) hv y,zero_add]
lemma Opera :∃ D: Law Z!,office S he U D:=by
    let M:= FUND S he U; let P:=countingBasis X! G; let H:= iteratedFDeriv ℝ 2 Pz 0; let Z(a b:Z!):=dotProduct (cash P a) (M *ᵥ cash P b); have hv(x y):Z x y=H ![(0,x),(0,y)]:= (tollY S he U h t x y).symm; have hh(x y): Z x y= Z y x:=by rw [hv,hv,Work.F03.hessian_symmetric]; exact (viewer t h.2.1).origin.of_le le_top
    let T:=ContinuousLinearMap.inr ℝ K! Z!; have hy(i:Z!) :∃ A:Dual' Z!,Z i=A:=by
         let Q:= (H.curryLeft (0,i)).curryLeft; have hp(x): Z i x= Q (T x) ![]:=hv ..; exact ⟨{toFun:=Z i,map_add':=fun x y=>by simp_rw [hp]; rw [map_add,map_add]; rfl,map_smul':=fun c x=>by simp_rw [hp]; rw [map_smul,map_smul]; rfl },rfl⟩
    obtain ⟨A,hA⟩:= giraffe_addendum hy hh; refine ⟨Libra.giraffe A (fun x y=>by rw [hA,hA]; exact hh ..) ?_,hA⟩
    intro x hx; rw [hA];unfold Z; let w:= cash P x; have hf:w≠0:=fun p=> hx (P.equivFun.injective (p.trans (P.equivFun.map_zero).symm)); change 0<w ⬝ᵥ _;exact star_trivial w ▸ (ulk_force S he U).dotProduct_mulVec_pos hf
structure FibreRep (A:Alps K T i v)(g:Bid.Dir G c→ AxisChart G X!)(b:ℝ) where
    L:Fiber (Keys G (Body 1 c)) G (forest S.ratio he).Free
    meter: L.f=ᶠ[𝓝 0] fun x=> (pane X! t A.clip A.live x)-pane X! t A.clip A.live 0
    serves: L.w=ᶠ[𝓝 0] OreA S he t A b
    M: L.M= fderiv ℝ (cabin g) 0
    P0: office S he U L.Q
lemma enrol (b:ℝ)(hs:G.Simple): Nonempty (FibreRep S he U t A g b):=by
      let M:= Pz; let W:= OreA S he t A b; have hx:ContDiffAt ℝ ω M 0:= (viewer t h.2.1).origin; have hp: ContDiffAt ℝ ω W 0:= by unfold W OreA; exact ((hx.const_smul (-b)).sub ((sophok X! A.pays).1.comp (f:=Prod.snd) 0 contDiffAt_snd)).exp
      let Q:= M-fun _=> M 0; obtain ⟨f,hf,hK⟩:= arcShape (f:=Q) (hx.sub contDiffAt_const); obtain ⟨w,hw,hL⟩:= arcShape hp; let Z:= fderiv ℝ (cabin g) 0; obtain ⟨D,hP⟩:= Opera S he U t h
      refine ⟨{ L:={f:=f,w:=w,C:=hf, H:=?_, HC:= hp.of_le le_top|>.congr_of_eventuallyEq hL,hw:=by rw [hL.eq_of_nhds]; exact Real.exp_pos _,hv:=hw,M:=Z,Q:=D,split:=?_ }, meter:=hK, serves:=hL, M:=rfl, P0:=hP }⟩
      · refine ⟨((hx.sub (contDiffAt_const (c:=M 0))).of_le le_top|>.congr_of_eventuallyEq hK),by rw [hK.eq_of_nhds]; exact sub_self _,fun i=>?_⟩; unfold jet; rw [iteratedFDeriv_one_apply,hK.fderiv_eq]; unfold Q; rw [fderiv_sub (hx.differentiableAt (by simp)) (differentiableAt_const _), show fderiv ℝ M 0=0 from pegZ S he U t h hs,fderiv_const_apply]; simp
      intro x y; let A':= (x,Z x); let C:= ((0:K!),y); let T:= iteratedFDeriv ℝ 2 M 0; have hG(u:K! × Z!) : jet f 2 u=T ![u,u]/2:=by
          unfold jet; rw [(hK.iteratedFDeriv ℝ _).eq_of_nhds,iteratedFDeriv_sub_apply (f:=M) (hx.of_le le_top) contDiffAt_const]; simp [iteratedFDeriv_const_of_ne]; rw [show (fun _ :Fin 2=>u)=![u,u] from funext fun i=>by fin_cases i<;>rfl]; unfold T;norm_num;ring
      have hY:T ![A',C]=0:=by rw [show A'=fieldT (cabin g) x from (folds t h.2.1 _).symm]; exact (viewer t h.2.1).hedge ..
      have hQ:T ![C,A']=0:=(Work.F03.hessian_symmetric (hx.of_le le_top) ..).trans hY; have hu:T ![A'+C,A'+C]=T ![A',A']+T ![C,C]:=by rw [show T ![A'+C,A'+C]=T ![A',A'+C]+T ![C,A'+C] from DFunLike.congr_fun (T.curryLeft.map_add A' C) ![A'+C],show T ![A',A'+C]= T ![A',A']+T ![A',C] from DFunLike.congr_fun ((T.curryLeft A').curryLeft.map_add A' C) ![],show T ![C,A'+C]= T ![C,A']+T ![C,C] from DFunLike.congr_fun ((T.curryLeft C).curryLeft.map_add A' C) ![],hQ,hY,zero_add,add_zero]
      rw [show (x,Z x+y)=A'+C from Prod.ext (add_zero _).symm rfl,hG,hG,hu,hP,← tollY S he U h t]; unfold T; ring
end YM.OPE.Cascade.Rill
