import YM.FVAAlt2.Turn.Sat
import YM.FVAAlt2.Home.Bridge1
import YM.FormalOPE.RG10.Compass.Kettle
/-! H-transform of off-shell stencil interpolation in its supplied Loom.Position dictionary.
 Uses arbitrary Sound&Chosen (orientation of ACTUAL stencils, not any projected periodic
 version). Hence exact off-shell W coordinates transformation, not leading regulator inversion. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home
open Function Finset Lattice Labels Source Filter MeasureTheory
open MS MS.Koszul MS.Theater MS.FVA MS.FVA.Motions MS.Menus MS.Local.Physical MS.Native MS.Lifting MS.Land MS.Wind
open MS.Cylinder MS.Landau MS.Landau.Detect MS.Bare MS.Native.Paint MS.Cylinder.Taylor MS.Native.Orient MS.Cylinder.Lab MS.Native.Chart
open FormalOPE FormalOPE.RG10 PertExtension PertExtension.Orb PertExtension.Orb.SlotEvaluation PertExtension.LatticePT
open scoped Topology BigOperators ContDiff Classical
variable {G: Gauge} {d k h:ℕ} {R:Labels.Frame G d} (s:Signed) (S:SectionData R){H:Hol G}(hS:S.Sound H)(hp:Bid.pop S)
local notation "βF"=> R.Coeff
variable (i:R.Index)
local notation "v"=> R.act s.ortho (Pi.single i 1)
local notation "A"=> R.Index
local notation "PX"=> pose s
local notation "J"=> univ.filter fun j=> R.grades i=R.grades j
lemma atomR(j:R.Index) : (↑(((v) j).re):ℂ)=(v) j:= by
   let w: R.Coeff:=Pi.single i 1; apply Complex.conj_eq_iff_re.mp; obtain h:= congr_fun (Extra.Histories.Motion.act_conj R w s.ortho) j; rw [show star w=w from ?_] at h; exact h.symm
   funext k; unfold w; by_cases he:k=i<;> simp [he]
include hS
lemma pose_root : PX (Shop.origin S i)= ∑ j∈(J), v j • Shop.origin S j:= by
   apply (enterEq ..).mp; refine Eventually.of_forall (fun n=>?_); rw [map_sum]
   let F'(j:A):= fieldAt S j (0:Site n)∘ nation; let hP(j:A):= ((v) j).re; have hh j: shown n (Shop.origin S j)=MS.Cylinder.region.symm (reads (F' j)):= Subtype.ext (Shop.doc_co ..)
   have hu : F' i ∘ Orient.affine s = ∑ j∈(J), hP j • F' j:= by
      funext z; unfold F' hP; simp_rw [Function.comp_apply,at_nation]; change InversionWard.Rotation.pullField s (0:Site n) S i 0 (nation z)= _; rw [InversionWard.Rotation.reorders s hS, Lattice.affine,Signed.act_zero, add_zero]; simp [Finset.sum_apply]
   change (shown n (PX (Shop.origin S i))).val= _; rw [travel_t,hh,pose_rule s (Shop.static S i n),hu, reads, ink_sum (F:=fun j=>hP j • F' j) _ _ (fun j _=> (Shop.static S j n).const_smul (hP j) ) ]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [map_smul, ← atomR s i j, Shop.doc_co ]; exact ink_smul _ (Shop.static S j n) _
lemma levels_plane : PX ∘ Shop.priceS S i = ∑ j∈(J),v j • Shop.priceS S j := by
   funext k; simp only [Finset.sum_apply, Pi.smul_apply,Function.comp_apply, Shop.priceS, MS.Book.levels ]; rw [ MS.Book.poseModel, pose_root s S hS i, map_sum ]; apply sum_congr rfl; intro j hj; rw [ (mem_filter.mp hj).2,map_smul]
-- raw linear, extends
private def priceV (S:SectionData R): R.Coeff →ₗ[ℂ] (ℕ→ Dot G Cover) where
    toFun x:= ∑ i:R.Index,x i • Shop.priceS S i
    map_add' x y:= by simp_rw [Pi.add_apply,add_smul,Finset.sum_add_distrib]
    map_smul' c x:= by simp_rw [Pi.smul_apply, smul_eq_mul,mul_smul]; rw [Finset.smul_sum]; rfl
omit hS
lemma price_off (S:SectionData R) (i:R.Index) : priceV S (Pi.single i 1)=Shop.priceS S i:= by
   unfold priceV; simp only [LinearMap.coe_mk,AddHom.coe_mk,Pi.single_apply,ite_smul,zero_smul,one_smul]; simp
include hS
lemma level_pose (u:R.Coeff): PX ∘ (priceV S u)= priceV S (R.act s.ortho u):= by
 let S₀ (i:R.Index):= (Pi.single i 1:R.Coeff); have h(u:R.Coeff): u=∑ i:R.Index,u i • S₀ i:= by symm; funext; simp [S₀,Finset.sum_apply,Pi.single_apply,mul_ite]
 let M:= priceV S; nth_rw 1 2 [h u]; funext t; simp_rw [comp_apply,map_sum, map_smul,Finset.sum_apply, Pi.smul_apply]; -- stuck M? remove
 rw [map_sum]; apply sum_congr rfl; intro i _; rw [map_smul, show priceV S (S₀ i) = _ from price_off S i]; congr 1; rw [ show PX (Shop.priceS S i t) = _ from congr_fun (levels_plane s S hS i) t ]; unfold priceV;
 dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; apply congr_arg (fun f:ℕ→ Dot G Cover=> f t); apply sum_subset (Finset.subset_univ _); intro j _ hj; rw [show R.act s.ortho (S₀ i) j=0 from InversionWard.Rotation.compare s (by simpa only [mem_filter,mem_univ,true_and] using hj), zero_smul]
local notation "T"=> topMatrix S H hS hp
def weighted (S:SectionData R) (hS:S.Sound H)(hp:Bid.pop S) : Label G d→ₗ[ℂ] (ℕ→ Dot G Cover):= priceV S ∘ₗ ((topMatrix S H hS hp).inverse (covarianceSymbol G)) ∘ₗ R.coords.toLinearMap
include hp
lemma weight_s (u:Label G d) : PX ∘ weighted S hS hp u= weighted S hS hp (Labels.tensor s.ortho u):= by rw [weighted]; simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,level_pose s S hS, Spiral.ordered s hp hS,← R.act_coords]; -- commute orientation
variable {B: Deck G}
lemma funds (u: B.BIndex d k): weighted S hS hp (Shop.seat B u) = Shop.RBook B S hS hp u:= by
   let X:= R.coords (Shop.seat B u (d:=d)); let K:=(T).conversion (covarianceSymbol G); have he : X=∑ i, X i • (Pi.single i 1:βF):= by funext j; symm; simp only [Finset.sum_apply]; simp [Pi.single_apply,mul_ite]
   have hm: K.symm X=Shop.valueP B S hS hp u:= by
     funext j; rw [he,map_sum,Finset.sum_apply]; unfold Shop.valueP; refine Finset.sum_congr rfl fun i _=>?_ ; rw [map_smul, Pi.smul_apply, Vertex.true_coefficients]; rfl
   change (∑ i:A, K.symm X i • Shop.priceS S i)=_; rw [hm];rfl
end YM.FVAAlt2.Home
