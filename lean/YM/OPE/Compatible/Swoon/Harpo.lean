import YM.OPE.Compatible.Swoon.Real
/-!
# Color trace of yy-charge exact vanish. Based on full-F Hess positive, all centers bought
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}
variable (S:StepData c f)(he:Odd S.ratio.count.val)(H:Even c.val)(X: Plot H)
local notation "μ"=> even_both S.ratio H
local notation "X!"=> forest S.ratio he
local notation "W!" => stroll S he H X
local notation "V!" => valley S he H X
local notation "Z!" => AxisChart G X!
local notation "Qµ"=> Blocx S he H
local notation "P!" => Keys G X.Free
local notation "J!" => Keys G (Blocx S he H)
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass Coin Pilot
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v}{D:Alps K T d u} (U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:licensed S he U A.clip A.live L A.sky g)
variable (V:Bor H D b)(Y:Elm A S H t r){P:ChartRatio G}(ht:LocalRatio P)
local notation "LK"=> Keys G (Stand.Free (stroll S he H X))
local notation "CL"=> Bid.Dir G c × AxisChart G X!
def InV (G:Gauge): Keys G (Blocx S he H)→L[ℝ] (Bid.Dir G c × AxisChart G X!) := ContinuousLinearMap.inr ℝ _ _ ∘L EchoV S he H G
def Busk (v:G.El): (Bid.Dir G c × AxisChart G X!) ≃L[ℝ] (Bid.Dir G c × AxisChart G X!) := LinearEquiv.toContinuousLinearEquiv ((glint (Body 1 c) v).prodCongr (glint (forest S.ratio he).Free v))
lemma Buske (v:G.El)(x:J!): Busk S he v (InV S he H G x)= InV S he H G (glint _ v x):=by
       let y:=glint Qµ v x; change (glint _ v 0,glint _ v (EchoV S he H G x))=(0,EchoV S he H G y); refine Prod.ext ((glint _ v).map_zero) ?_; ext1 p; change G.adjoint v (EchoV S he H G x p) = EchoV S he H G y p; rw [echoVi,echoVi]; split; exact map_neg ..;rfl
lemma BuskC (v:G.El)(x:Keys G (Limb H)):glint _ v (cloak H x)=cloak H (glint _ v x):=by
       ext1 i; rcases i with ⟨k,p⟩; obtain ⟨a,rfl⟩:= axisEquiv.surjective p; change G.adjoint v (cloak H x (k,coord a))=cloak H (glint _ v x) (k,coord a); simp_rw [cloak_at,Streamer.hover]; split; exact map_neg ..; rfl
lemma susK (v:G.El)(ha:S.patch.Branches S.kernel G): pane X! t A.clip A.live ∘ Busk S he v=pane X! t A.clip A.live:=by
       funext p; let u:= represent p.1; let W:=fieldF X! p.2; let x:= fun (_:Site f)=>v; let y:=x ∘ S.ratio.embed; let V:= Busk S he v p; have hx:fieldF X! V.2=Lattice.gauge x W:=by
            ext1 i; by_cases h:i∈ (forest S.ratio he).trunks
            · rw [show fieldF X! V.2 i=1 from (forest S.ratio he).on_tree _ ⟨i,h⟩]; unfold Lattice.gauge; rw [show W i=1 from (forest S.ratio he).on_tree _ ⟨i,h⟩]; simp [x]
            let k:(forest S.ratio he).Free:=⟨_,h⟩;unfold Lattice.gauge; rw [show W i=put p.2 k from (forest S.ratio he).off_tree _ k,show fieldF X! V.2 i=put V.2 k from (forest S.ratio he).off_tree _ k]; exact congr_fun (Glass.patchZ v p.2) k
       have hp : represent V.1=Lattice.gauge y u:=by
            ext1 i; unfold Lattice.gauge u; simp only [Work.F03.represent_link]; exact YM.Stationary.adjoint_exp ..
       change mainTerm _ _ (fieldF X! V.2)+ noiseTaylor S (represent V.1) (fieldF X! V.2) t= _; rw [hx,hp, caring]; exact congr_arg (·+ noiseTaylor S u W t) ((A.fullK 0).stand f x W)
       exact ha
include h t
lemma stillZ (v:G.El)(m:ℕ)(x:Fin m→ CL): iteratedFDeriv ℝ m (pane X! t A.clip A.live) 0 (Busk S he v ∘ x)= iteratedFDeriv ℝ m (pane X! t A.clip A.live) 0 x:=by
      let L:=(Busk S he v).toContinuousLinearMap; let Q:=pane X! t A.clip A.live; calc
          _= iteratedFDeriv ℝ m (Q ∘ L) 0 x:=by rw [jets_linear _ ((viewer t h.2.1).origin.of_le le_top)];rfl
          _= _:=by rw [show Q ∘ L=Q from susK S _ t v h.1.cover]
lemma BuskT (v:G.El)(x: Keys G (Limb H)): Busk S he v (fieldT (cabin g) (cloak H x))=fieldT (cabin g) (glint _ v (cloak H x)):=by
     have hp:=viewer t h.2.1; let Q:= Busk S he v; let z:= fieldT (cabin g) (cloak H x); let y:=fieldT (cabin g) (glint _ v (cloak H x)); have hx:(Q z).1=y.1:=by change glint _ v z.1=y.1;rw [show z.1=cloak H x from hp.rim _]; exact (hp.rim _).symm
     let M:= iteratedFDeriv ℝ 2 (pane X! t A.clip A.live) 0; have hv(i:Z!): M ![Q z,(0,i)]= M ![y,(0,i)]:=by
          obtain ⟨a,rfl⟩:= (glint _ v).surjective i; let k:=((0:Bid.Dir G c),a); rw [show ((0:Bid.Dir G c),glint _ v a)=Q k from Prod.ext (glint _ v |>.map_zero.symm) rfl]; calc
             _=M (Q ∘ ![z,k]):= congr_arg M (funext fun i=>by fin_cases i<;>rfl)
             _= M ![z,k]:=stillZ S _ U t h _ _ _
             _=0:=hp.hedge _ _
             _=M ![y,Q k]:=by rw [show Q k=(0,glint _ v a) from Prod.ext ((glint _ v).map_zero) rfl]; exact (hp.hedge _ _).symm
     change Q z=y; apply sub_eq_zero.mp; let w:=(Q z).2-y.2; have hh:Q z-y=(0,w):=Prod.ext (by rw [Prod.fst_sub,hx,sub_self]; try rfl) rfl; rw [hh]; refine Prod.ext rfl ?_
     have hu:M ![Q z-y,(0,w)] =0:=by
         change M.curryLeft (Q z-y) _=_; rw [map_sub]; exact sub_eq_zero.mpr (hv w)
     let P:= countingBasis X! G; rw [hh,tollY S he U h t] at hu; apply P.equivFun.injective; change cash P w=P.equivFun 0; rw [map_zero]; by_contra ha
     exact ((ulk_force S he U).dotProduct_mulVec_pos ha).ne' (by rw [star_trivial]; exact hu)
end YM.OPE.Cascade.Rill
