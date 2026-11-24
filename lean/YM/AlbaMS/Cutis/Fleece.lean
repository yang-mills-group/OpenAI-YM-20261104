import YM.AlbaMS.Cutis.Silhouette

/-! # color-blind movement in mixed words -/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis.Winter
open Set Function Filter LinearMap Matrix IsNilpotent
open scoped BigOperators Classical Topology Matrix InnerProductSpace ENNReal
open Bric Coil Loft Inlay Inlay.Net Odom Lattice Nexus
variable {R : Type*}[CommRing R]{G:Gauge} {n:Side}(T:Tune R)
abbrev LightQ (G:Gauge)(n:Side)(R:Type*)[CommRing R]:= Heave G (Edge (Site n)) (Site n) R
abbrev Beam := (lead G n).atlas T.D
abbrev Stick := (spark G n).atlas T.D
lemma citizen (h:Even n.val)(c:G.Color): (lead G n).firm (hill c)=0:=by
  let P:= thorn n; let W:= Winter.prop n
  have hp:(P*W)ᵀ*(P*(1-W))=0:=by rw [transpose_mul,show Wᵀ=W from orth h, ← Matrix.mul_assoc _ P, Matrix.mul_assoc _ Pᵀ P, show Pᵀ*P=(2:ℝ) •1 from stalkSeal h, Matrix.mul_smul, Matrix.mul_one,Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_one,show W*W=W from self_pair h,sub_self,smul_zero]
  have ht: (lead G n).kᵀ*dash (Arm n) c*(lead G n).a=0:=by
    rw [lore_K,lore_A,Matrix.mul_assoc, share, ← Matrix.mul_assoc]; unfold dotC; rw [chip_t, chip_prod,hp,chip_zero,Matrix.zero_mul]
  have hx (j :Flit G (Vtx n)): (lead G n).firm (Loft.L ℝ j)=0:=by rw [Wire.actL, lore_S]; simp
  rw [hill,map_add]; change (lead G n).firm (∑ i: ink1 G n,K ℝ i * ∑ j: ink1 G n, dash (Arm n) c i j • A ℝ j)+_=0; rw [Wire.block,ht,map_sum]; simp_rw [Wire.firm_mul,hx]; simp
lemma age_b (X : LightQ G n R) : (Beam (G:=G) (n:=n) T).firm X=((squash G n).atlas T.D).firm (T.crossT (walkT n G true) X):=by
  rw [Wire.crosses, Wire.sketch];
  have ht : Beam T=((lineWire G n).atlas T.D).compose ((squash G n).atlas T.D):=by
    unfold Beam lead Wire.atlas Wire.compose; congr 1<;> simp only [Matrix.map_mul]
  rw [ht]; rfl
lemma squeeze (h:Even n.val)(X:LightQ G n R)[Algebra ℚ R](hs: FinRank X):
    Fritz.eval (drive (G:=G) (n:=n) T).hop ((Beam T).firm X)= Fritz.eval (drive (G:=G) (n:=n) T).hop (T.crossT (walkT n G true) X):=by
  rw [age_b]; rw [Wire.crosses]; rw [← Wire.draws _ _ _ (Wire.shoot_n _ X hs)]; congr 1; rw [show drive (n:=n) (G:=G) T= _ from rfl, ← Wire.plays, squash_price G n T.a h T.ha] -- dummy
-- drift converted across any Tune.D to Dir; no assumption input real. 
private def sendB (x : Sand G n) : G.Color:= (-(mean n* shrub n true) 0 x.1) • base G x.2
lemma moving (x:Sand G n)(v:Flit G (Vtx n)): (spark G n).c v x-(lead G n).c v x=fill (sendB x) v:=by
  have hb : (spark G n).c=dotC G (run n):=by apply Matrix.mul_one
  have ha:(lead G n).c=Ψ (walkT n G true):=by apply Matrix.mul_one
  rw [ha,hb,paidS, ← Matrix.sub_apply]; simp only [run,dotC]; rw [chip_sub];
  have ht (i:Vtx n) : (mean n* shrub n true) i x.1=(mean n * shrub n true) 0 x.1 := by rw [Matrix.mul_apply, Matrix.mul_apply]; rfl
  have hh : ∀ (X Y: Matrix (ink0 G n) (Sand G n) ℝ), X-Y-X= -Y:=by intro X Y; abel
  rw [hh,Matrix.neg_apply]; simp_rw [chip, Matrix.of_apply,ht,fill,sendB,map_smul,coef_base]; by_cases h:v.2=x.2; simp [h]; simp [h,Ne.symm h]
private lemma crest (X: LightQ G n R)(x):
    drift Finset.univ (Beam T).fee (Stick T).fee x X=∑ i:Leaf G (Arm n) (Vtx n), T.D ((spark G n).fee i x-(lead G n).fee i x) • D i X:=by
  unfold drift Beam Stick; simp_rw [LinearMap.sub_apply,drip_apply,map_sub, Wire.linked]; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => (sub_smul ..).symm
lemma drift_color (U: LightQ G n R)(x): ∃ c:G.Color, drift Finset.univ (Beam T).fee (Stick T).fee x U= air (fun i=>T.D (fill c i)) U:=by
  rw [crest]; rcases x with (x|x)|(x|x)
  case inr.inl =>
    refine ⟨sendB x,?_⟩; simp only [air_ap, Fintype.sum_sum_type, Wire.fee, moving, map_zero,zero_smul, Finset.sum_const_zero, add_zero,zero_add,sub_self]; -- parser
  all_goals refine ⟨0,?_⟩
  all_goals simp only [air_ap,Fintype.sum_sum_type,Wire.fee, show (spark G n).l=(lead G n).l from rfl,show (spark G n).a=(lead G n).a from rfl, show (spark G n).k=(lead G n).k from rfl, fill,map_zero,sub_self,zero_smul, Finset.sum_const_zero, add_zero]
end YM.MSBar.Cutis.Winter
