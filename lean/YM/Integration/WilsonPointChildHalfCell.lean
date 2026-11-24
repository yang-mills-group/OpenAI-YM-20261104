import YM.Integration.WilsonPointChildTestJet
import YM.Integration.WilsonPointChildCoveredTariff

/-! The covered normalized pinned row rendered on the actual coefficient test
    and on its native singleton tensor, prior to selecting the test value. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildHalfCell
open YM Lattice RG Wilson Filter Function Finset PowerSeries Next.Free Stationary PhysicalNext.Repeat.Legato Next.Foundations
open Laurent FormalBulk08 Reef Flat Lava Lotus Shore Mesa Gorge Rift Kemp Pose Aster Roof Dawn
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open WilsonPointChildFiledPress WilsonNeutralPointCourse WilsonPointChildTestJet
open scoped Topology ContDiff ENNReal Matrix BigOperators Classical
variable {G:Gauge}{ι α:Type}{d D r:ℕ}
local instance studio_group (D:ℕ):NormedAddCommGroup (Studio D):=inferInstance
local instance studio_space (D:ℕ):NormedSpace ℝ (Studio D):=inferInstance
local instance gallery_group (D:ℕ):NormedAddCommGroup (Dawn.Gallery D):=inferInstance

def kernel (levels:ι→ℕ)(s:ι)(z:Chamber)(K:dock Cover α r→Dawn.Gallery (levels s)):
    dock Cover α r→Pen levels {s}:=fun x=>petal levels s ((K x).comp (extend (levels s) z))

theorem evaluated (levels:ι→ℕ)(s:ι)(z:Chamber)(K:dock Cover α r→Dawn.Gallery (levels s))
    (x:dock Cover α r)(V:Case levels):
    touch V {s} (kernel levels s z K x)=K x (extend (levels s) z (V s)):=petal_hit .. 

theorem funded (levels:ι→ℕ)(p:ι → Cover)(s:ι)(z:Chamber){B b:ℝ}(K:dock Cover α r→Dawn.Gallery (levels s))
    (paid:Wig terrain p b B {s} K):Wig terrain p b (rent (levels s)*B) {s} (kernel levels s z K):=by
  have C:0≤ rent (levels s):=Finset.sum_nonneg fun _ _=>norm_nonneg _
  refine ⟨mul_nonneg C paid.1,fun x=>?_⟩
  have h:= (petal levels s).le_opNorm ((K x).comp (extend (levels s) z))
  have h1:= (ContinuousLinearMap.opNorm_comp_le (K x) (extend (levels s) z)).trans
    (mul_le_mul_of_nonneg_left (price z) (norm_nonneg _))
  have h2:=mul_le_mul_of_nonneg_right (paid.2 x) C
  exact h.trans ((mul_le_mul_of_nonneg_right (petal_bound levels s) (norm_nonneg _)).trans
    (by simpa only [one_mul,mul_left_comm,mul_comm,mul_assoc] using h1.trans h2))

theorem original (R:Run G)(wood:Primer.Families R.family)(a:G.ColorIndex)(depth:d<D)(o:Loc G 1)(simple:G.Simple)
    {orders:ℕ→ℕ}(granted:WilsonWindowFormalPurchase.Canonical orders R.kit)
    (slow:∀j,((R.family.S.block j).val:ℝ)≤Real.log (RG16.Lambda R.family.path.levels j))
    {E:ℕ}(weak:WilsonPointChildInverseIncome.Weak R wood a depth o E)
    (fwd:WilsonPointChildInverseIncome.Forward R wood a depth E){η:ℝ}(hp:0<η):
    ∀ᶠi:ℕ in atTop,∀N,i≤N→∀v:Letter (R.family.labels.level d),∀e≤E,∀r,
    ∃K:chain (edgeL G) r→Pen (fun _:Unit=>D) {()},
      (∀x (V:Case (fun _:Unit=>D)) (q:Studio D),
        (∀t:Spring D,notch t.val (paper_fits t) q=(V ()).val (finger (paper_fits t)) zeroC)→
        touch V {()} (K x)=filed R wood a depth (fun _=>0) N i v q e r x) ∧
      Wig terrain (fun _:Unit=>0) (width R i) (rent D*((R.family.path.levels.clock.hatBeta i)^η)) {()} K:=by
  filter_upwards [WilsonPointChildCoveredTariff.original R wood a depth o simple granted slow weak fwd hp] with i h
  intro N live v e cap r
  obtain ⟨A,read,paid⟩:=h N live (fun j=>0) v e cap r
  let Y:=filed R wood a depth (fun _=>0) N i v
  let L:chain (edgeL G) r→Pen (fun _:Unit=>D) {()}:=kernel (fun _:Unit=>D) () zeroC A
  have fit:Wig terrain (fun _:Unit=>0) (width R i) (rent D*((R.family.path.levels.clock.hatBeta i)^η)) {()} L:=
    funded (fun _:Unit=>D) (fun _:Unit=>0) () zeroC A paid
  refine ⟨L,?_,fit⟩
  intro x V q same
  have field:Y (extend D zeroC (V ()))=Y q:=(WilsonPointChildTestJet.original R wood a depth N i v (V ()) q same).symm
  exact ((evaluated (fun _:Unit=>D) () zeroC A x V).trans (read x _)).trans
    (congrArg (fun Z:Mesa.Pot G=>Z e r x) field)

end YM.Integration.WilsonPointChildHalfCell

