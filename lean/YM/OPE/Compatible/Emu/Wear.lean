import YM.OPE.Compatible.Emu.Dent
/-!
# Spine chart and partial Law. Untruncated Hess.Clauses
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score Tree Woody Next.Free FreeResolvent
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance
variable {i j d k m r l:ℕ}{n:Side}{K:Sponsor G}{T:Seasons K}{v:ℝ}
local notation "L!"=>Body 1 n
local notation "P!"=>Chamber G r
variable (hp:Board n (r+1)) (A:Alps K T i v)(ha:4 ≤ i)
local notation "F!"=>Bid.Dir G n
noncomputable abbrev metP := Prog K.K A.gear G n
lemma sheen (x y:F!)(ha:4 ≤ i): iteratedFDeriv ℝ 2 (Dune A (n:=n)) 0 ![x,y]= flats G n x ⬝ᵥ (metP A*ᵥ flats G n y):=by
        rw [S32 A ha, flatX,flatX]; unfold metP Prog; rw [Alps.root,Op_stays ha]
lemma east (h:Board n (r+2))(x:P!)(he:4≤ i):let X:= flats G n (sailT G hp x);2*damp r A.clip*‖x‖^2 ≤ dotProduct X (metP A *ᵥ X):=by
        intro X; let Q:=diagonalQ A.clip A.live h A.pays hp x; rw[← (chartK A.live A.clip n A.pays).2,A.inkTot he] at Q; change _ ≤ dotProduct X (metP A (n:=n) *ᵥ X); unfold X; rw [metP,flatX,Prog, ← Op_stays he]; exact Q
section C
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
noncomputable def chrom (f:F→ℝ): F→ₗ[ℝ] Dual' F:= by
     let K:=fderiv ℝ (fderiv ℝ f) 0; exact {toFun:=fun x => (K x).toLinearMap,map_add':=fun x y => by rw [map_add];rfl,map_smul':=fun x y=>by rw [map_smul];rfl}
lemma podium (f:F→ℝ)(x y:F):chrom f x y=iteratedFDeriv ℝ 2 f 0 ![x,y]:=by rw [iteratedFDeriv_two_apply]; rfl
lemma turnsT (f:F→ℝ)(h:ContDiffAt ℝ 2 f 0):∀ x y,chrom f x y=chrom f y x:=by intro i j; rw [podium,podium]; exact Work.F03.hessian_symmetric h i j
variable [FiniteDimensional ℝ E][FiniteDimensional ℝ F]
noncomputable def vertex (R: E →L[ℝ] F)(K:F →ₗ[ℝ] Dual' F): E →ₗ[ℝ] Dual' E:= R.toLinearMap.dualMap ∘ₗ K ∘ₗ R.toLinearMap
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in lemma vtx (R:E →L[ℝ] F)(K:F →ₗ[ℝ] Dual' F)(x y:E):vertex R K x y= K (R x) (R y):=rfl
noncomputable def soar (R:F →L[ℝ] E) (K:E→ₗ[ℝ] Dual' E) (he:∀ x y,K x y=K y x) (hp:∀ x:F,x≠0→0 < K (R x) (R x)): Law F:=Libra.giraffe (vertex R K) (fun x y=>by rw [vtx,vtx]; exact he _ _) hp
structure SiteL (R:E→L[ℝ] F)(K:F →ₗ[ℝ] Dual' F) (P:Law E) :Prop where
       hike: ∀ i j,K i j=K j i
       earns :P.P=vertex R K
variable (R:E →L[ℝ] F)(L:F →ₗ[ℝ] Dual' F) (P:Law E)
namespace SiteL
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in lemma sat (h:SiteL R L P) (x y:E):L (R x) (R y)=P.P x y:=by rw[h.earns]; exact (vtx ..).symm
noncomputable def pour:F→L[ℝ] E:= LinearMap.toContinuousLinearMap ((P.inverse ∘ₗ R.toLinearMap.dualMap)∘ₗ L)
noncomputable def mate:F→L[ℝ] F:= ContinuousLinearMap.id ℝ _-R ∘L pour R L P
lemma loan (x:F)(y:E): L x (R y)= P.P (pour R L P x) y:=by change L x (R y)=P.P (P.inverse (L x ∘ₗ R.toLinearMap)) y; rw[Law.applies]; rfl
lemma pillar (h:SiteL R L P)(x:E): pour R L P (R x)=x:=by
       change P.inverse (L (R x)∘ₗ R.toLinearMap)=x; rw [show L (R x)∘ₗ R.toLinearMap=P.P x from LinearMap.ext (fun y=> h.sat _ _ _ x y),Law.solves]
lemma twin (h:SiteL R L P)(x:E): mate R L P (R x)=0:=by unfold mate; rw [_root_.sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,pillar R L P h,sub_self]
lemma along (h:SiteL R L P)(x:F): pour R L P (mate R L P x)=0:=by unfold mate;rw [_root_.sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,map_sub,pillar R L P h,sub_self]
lemma pen (h:SiteL R L P)(x:F)(y:E): L (mate R L P x) (R y)=0:=by rw [loan R L P,along R L P h,map_zero]; rfl
lemma alongQ (x:F):x= mate R L P x+R (pour R L P x):=by simp [mate]
lemma reduce (h:SiteL R L P)(x:F)(y:E): L (mate R L P x+R y) (mate R L P x+R y)= L (mate R L P x) (mate R L P x) + P.P y y:=by rw [L.map_add,LinearMap.add_apply,map_add,map_add,h.pen R L P,h.hike (R y) (mate R L P x),h.pen R L P,sat R L P h y y,zero_add,add_zero]
end SiteL
omit [FiniteDimensional ℝ F] in lemma SiteL.made (L:F→ₗ[ℝ] Dual' F)(H:E→L[ℝ] F)(c:ℝ)(hc:0<c)(ht:∀ i j,L i j=L j i)(hp:∀ x:E,c*‖x‖^2≤ L (H x) (H x)): ∃ B:Law E,SiteL H L B∧∀ x,c*‖x‖^2 ≤ B.P x x:=by
       let B:= Libra.giraffe (vertex H L) (fun x y=> ht _ _) (fun x hx=> (mul_pos hc (pow_pos (norm_pos_iff.mpr hx) _)).trans_le (hp x))
       exact ⟨B,⟨ht,rfl⟩,hp⟩
end C
include ha
lemma corner (h:Board n (r+2))(x:P!): 2*damp r A.clip*‖x‖^2 ≤ chrom (Dune A) (sailT G hp x) (sailT G hp x):=by
       rw [podium,sheen A _ _ ha]; exact east hp A h x ha
lemma station (hX:G.Simple)(h:Board n (r+2)):∃ B:Law P!, SiteL (sailT G hp) (chrom (Dune A)) B∧∀ x,2*damp r A.clip*‖x‖^2 ≤ B.P x x:=
       SiteL.made (chrom (Dune A)) (sailT G hp) _ (mul_pos (by norm_num) (dampK _ _)) (turnsT (Dune A) ((DuneAt A hX).sm.of_le le_top)) (corner hp A ha h)
end YM.OPE.Merchant
