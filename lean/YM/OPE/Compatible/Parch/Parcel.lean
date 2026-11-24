import YM.OPE.Compatible.Parch.Easel
/-!
# Lens linear geometry. AX and arcs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Claw
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score Tree Woody Next.Free FreeResolvent
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance Merchant Merchant.SiteL Stand
variable {i j d k m r l:ℕ}{n:Side}{K:Sponsor G}{T:Seasons K}{v:ℝ}
section
variable {D V W:Type}[Fintype D][Fintype W]
local notation "I!"=>Libra.Keys G D
local notation "J!"=>Libra.Keys G W
structure OrientX (R:Cascade.Score D V)(L:Libra.Keys G D→ₗ[ℝ] Dual' (Libra.Keys G D))(F:Libra.Keys G W→L[ℝ] Libra.Keys G D)(P:Law (Libra.Keys G W)) :Prop where
       hyst : SiteL F L P
       sh :∀ u:V→G.Color,L (gillS R u)=0
       act (g:G.El) (x:J!):F (glint _ g x)= glint D g (F x)
       adv (g:G.El)(x y:I!): L (glint D g x) (glint D g y)=L x y
namespace OrientX
variable {R:Cascade.Score D V}{L:Libra.Keys G D→ₗ[ℝ] Dual' (Libra.Keys G D)}{F:Libra.Keys G W→L[ℝ] Libra.Keys G D}{P:Law (Libra.Keys G W)}
variable (h:OrientX R L F P)
include h
lemma dry (x:V→G.Color): pour F L P (gillS R x)=0:=by change P.inverse ((F.toLinearMap.dualMap) (L (gillS R x)))=0; rw [h.sh,map_zero,map_zero]
lemma slide (x:V→G.Color) (y:I!) : mate F L P (y+gillS R x)=mate F L P y+gillS R x:=by
       rw [map_add,show mate F L P (gillS R x)= gillS R x from ?_]; unfold mate; rw [_root_.sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,h.dry,map_zero,sub_zero]
lemma rotL (x y:J!)(g:G.El): P.P (glint W g x) (glint W g y)= P.P x y:=by rw [← h.hyst.sat F L P,←h.hyst.sat F L P,h.act,h.act,h.adv]
lemma hullB (g:G.El)(x:I!): pour F L P (glint D g x)= glint W g (pour F L P x):=by
       have ht:Injective P.P:= fun i j hij=>by rw [← Law.solves P i,hij,Law.solves] -- wrong?
       apply ht; apply LinearMap.ext; intro y; obtain ⟨y,rfl⟩:= (glint W g).surjective y; rw [← loan F L P,h.act,h.adv, h.rotL,loan F L P]
lemma city (g:G.El)(x:I!): mate F L P (glint D g x)= glint D g (mate F L P x):=by unfold mate; rw [_root_.sub_apply,_root_.sub_apply, map_sub,ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,h.hullB, h.act]
local notation "VD"=>Fin (r+1)
variable (g:I!→ℝ)
omit h
noncomputable def ωDot (p:I!→ℝ)(x:I!)(r:ℕ): Dual' J!:=(FoldU.pop (Tensor.coeff p (r+1) 0) x (mate F L P x)) ∘ₗ F.toLinearMap
noncomputable def ν (p:I!→ℝ)(x:I!)(r:ℕ):J!:= P.inverse (ωDot (P:=P) (L:=L) p x r (F:=F))
include h
omit h in lemma Crest (p:I!→ℝ)(x:I!)(r:ℕ): rank p (r+1) x-rank p (r+1) (mate F L P x)=L x (F (ν p x r (P:=P) (L:=L) (F:=F))):= by
       unfold rank; rw[FoldU.popularity,loan F L P,P.turns]; unfold ν; rw[P.applies]; apply congr_arg; exact sub_eq_iff_eq_add'.2 (alongQ F L P x) -- unif
lemma frameS(p:I!→ℝ)(ht:LevelA R p)(he:ContDiffAt ℝ ω p 0)(x:V→ G.Color)(y:I!):ν (P:=P) (L:=L) (F:=F) p (y+gillS R x) r=ν (P:=P) (L:=L) (F:=F) p y r:=by
        unfold ν; congr 1; apply LinearMap.ext; intro z; let A:=Tensor.coeff p (r+1) 0; let g:=gillS R x; let m:=mate F L P; change (∑ i:VD,A (FoldU.tab (y+g) _ i (F z)))=∑ i:VD,A (FoldU.tab y _ i (F z)); apply sum_congr rfl; intro i _
        let v (j:VD):= if i=j then (0:V→G.Color) else x; rw [show FoldU.tab (y+g) (m (y+g)) i (F z)=(fun j=>FoldU.tab y (m y) i (F z) j+ gillS R (v j)) from ?_]; rotate_left
        · have hh:m (y+g)=m y+g:= h.slide ..; rw [hh]; funext j; unfold FoldU.tab; by_cases hp:j=i; · subst j; simp [v]
          rw[update_of_ne hp,update_of_ne hp,show v j=x from if_neg (Ne.symm hp)]; unfold FoldU.banner FoldU.rowP; split_ifs <;>rfl
        exact shiftY R ht he _ v
lemma FrameAd (p:I!→ℝ)(ht:LevelA R p)(he:ContDiffAt ℝ ω p 0)(x:I!)(g:G.El):ν (F:=F) (L:=L) (P:=P) p (glint D g x) r=glint W g (ν (F:=F) (L:=L) (P:=P) p x r):=by
       have hp:Injective P.P:=fun i j hij=>by rw[←Law.solves P i,hij,Law.solves]
       apply hp; apply LinearMap.ext; intro y; obtain ⟨y,rfl⟩:= (glint W g).surjective y; rw[h.rotL]; unfold ν; rw[P.applies,P.applies]; let A:=Tensor.coeff p (r+1) 0; let m:=mate F L P; let t:=glint D g; change (∑ i:VD,A (FoldU.tab (t x) (m (t x)) i (F (glint W g y))))=∑ i:VD,A (FoldU.tab x (m x) i (F y)); apply sum_congr rfl; intro i _; rw [h.act,show m (t x)=t (m x) from h.city g x,show FoldU.tab (t x) (t (m x)) i (t (F y))= t ∘ FoldU.tab x (m x) i (F y) from ?_]; exact entY _ ht.inherits he (FoldU.tab x (m x) i (F y)) g -- unif
       funext j; unfold Function.comp FoldU.tab FoldU.banner FoldU.rowP; by_cases ht:j=i; subst i; simp; rw [update_of_ne ht,update_of_ne ht]; split<;>rfl
end OrientX
end
end YM.OPE.Claw
