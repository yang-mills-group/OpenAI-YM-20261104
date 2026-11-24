import YM.MergeProof.Tanger
import YM.MergeProof.Wax

/-!
# A small Offer suffices to run the WHOLE marked budget, with small output
exponent-rent

The value-price line and the existing spatial derivative line can be billed
separately. No editing any of the customer hypotheses (Photo.Usable still on
the very same words and same advertisements of (exponential,E/K) output).
-/
set_option autoImplicit false
noncomputable section
-- use local namespaces near ancestors for ease, GapsContact module
namespace YM.Merge.Photo
open Function Filter Set Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond PhysicalNext.Repeat PhysicalNext.Repeat.Lotus Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι: Type} [Fintype ι] {G: Gauge} {c f L: Side} {S:StepData c f} {P:Teller G} {T: Tube G S} {R:Rep G f}
    {W a r σ E Λ μ x κ w C: ℝ} {Ñ: ChartRatio G}
    {Q: ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R) (Y:Cash W x μ L Q o C T R) (χ:Chi) {A: Rep G c}
open Ovens Switch Palette Blaze.March Multiple Ursell Trees Mixed Daisy OmitClusters Gas
variable {rA:ι→ℝ} {hl:ℝ → Finset ι → Code G c} {dk ex kr v e:ℝ}
set_option quotPrecheck false
namespace Usable

lemma remeter (h:Usable M Y χ A rA hl dk ex kr) (he:A.p.B=radiusB x)
    (hh:Bikes Q L μ x v e 0 0 0) : Usable M Y χ A rA hl (v+e)
        (2*(pledgeA L Q μ x 0 0 0*(1-sailUp Q L x)⁻¹)) kr:=by
  let p:= lace M Y rA 0
  have hW i:= fair M Y χ rA h.vacuum i 0
  have hs:Summable p:= (sizes M Y χ rA h.vacuum hh (le_refl 0)).2
  refine {h with exponent:= ⟨fun i=>2*p i,fun i=>?_, hs.mul_left 2,?_⟩}
  · have ht:= Switch.constant (ι:=ι) (fun U=>song M Y χ rA i U 0 ∅) ((hW i).rocket)
       (fun U=> Paid.tasting (hW i) U 0 ⟨le_rfl,zero_le_one⟩ ∅)
    change Paid _ (2 * _); rw[two_mul]; exact Paid.sub (hW i) ht
  rw[he]; intro i
  have hh:= budget_scale zero_le_two (lucent M Y χ rA h.vacuum hh (le_refl 0) i)
  convert! hh using 2; rename_i k; split_ifs <;> first | rfl | (unfold p; ring) | simp
end Usable
end YM.Merge.Photo

namespace YM.PhysicalNext.Repeat.Mallow.Many
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} (g:G.Simple) {X:Metals G} {D: Rolls X.p} {A : Alloy X D}
    {R: Factor A} {l v:ℝ} {N m n:ℕ}(hm:m<N) {Q: In A.B.a m n} (H: Spring R N m n l v Q)
local notation "L" => D.L (A.B.a.clock.J (m+1))
local notation "J" => A.B.a.clock.J (m+1)
local notation "Jp" => A.B.a.clock.J m
local notation "k" => Rain.lint R.target A m
local notation "Y" => R.target J Jp
local notation "Ze" => R.expense J Jp
local notation "Cμ" => (R.shape.μ J Jp)
local notation "y" => A.B.a.clock.hatBeta m
local notation "O" => Chi.canonical
local notation "B" => A.B.a.budget m
variable (x: Icc l v)
open YM.Merge
open MergeProof Menu
variable (hE : (Q x|>.p).supportExponent≥100)(hN : 100≤(H.result x).p.supportExponent)
    (hS: Arrives R.shape A.delay) (hF:Pungent R.shape A.delay)
include g hm hS hE hN hF
local notation "V"=> A.B.a.clock.op m n
local notation "d0"=> sandboxK H x
set_option quotPrecheck false
local notation "b'"=> (B).supportExponent

-- strengthened variant of ripe in MergeProof/Tanger. Keep the old shipPrice
-- hypothesis (will charge it order-independently) and supplement with meter
-- using zero test derivative since only for hitPrice, hence no new Mallow.Arena
set_option maxHeartbeats 640000 in
lemma dawn (hZ:HasSlots ((Q x).p) ((Q x).activities)) {N':ℕ} {v' a e:ℝ} (hp:0≤v')
    (hc:Palette.shipPrice L Y y N' v') (hk:Bikes Y L Cμ y (Ze).earn e 0 0 0)
    (hA:2*(pledgeA L Y Cμ y 0 0 0*(1-sailUp Y L y)⁻¹) ≤ a) :
    Volant (V) d0 N' ((Q x|>.p.supportExponent)-4) v' (b'+1/2) (b'+1) a (straw Cμ L G y):=by
   let Rπ:= houseS H x; have hC:=hS _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)
   have hD:=ripe g hm H x hE hN hS hF hZ hp hc
   refine {hD with reserves:=?_}
   intro P hpP hP ι hι o r C b hb hQ ht
   have hΞ:= Opera.protocol A.B hm R.pledging.conducts.full (n:=n); obtain ⟨A₀,ba,q,t',z,F'₀,t₃,t₄,t₅,t₆,k',hB,hX,N₀,hN'⟩:=hC.1.2 _ _ _ _ hΞ (Q x) _ (houseS H x)
   let M i:= (b i).M; let a' i:= sumFee (b i) r
   have he : (B).supportExponent+3 ≤ (Ze).earn :=by
      have he':= R.pledging.agenda _ _ (step_paid A.B.a m)|>.1; rw [Rain.jersey (A:=A) (m:=m)|>.2.2.1]; linarith
   have hV:Palette.Plot M Rπ a' := Photo.bidding _ C r hb b o hC.1.1 (by rw [Rπ.laws.intake.sizes, Rπ.laws.data.funds.length_eq]; exact hB.covers) (by
        change 4 ≤ (Y).exp+_+_; change 100 ≤ b' at hN; linarith only [he,hN,(Ze).worth,(Ze).first,(Ze).second,(Y).usable,(Y).pos]) hE hp ht hQ hc
   let F:=pupilK H x M a'; let P':=(Q x).p
   have hv := Photo.Usable.remeter M (houseS H x) O (Many.usable g hm H x M a' N₀ hS hB hV) rfl hk
   obtain ⟨RH,b0,hR,hX,hb',hP',he',hZ',hW'⟩ := (Photo.shade _ _ _ F _ _ _ hb d0 b hD.propagate (fun i=>by intro j hj; obtain ⟨i',hi,hj⟩:= mem_image.mp hj; subst j; exact mem_image_of_mem _ (ht.sites _ (mem_image_of_mem _ hi))) hv (crowd2 g hm H x M a' N₀ hF hB hV) rfl (add_nonneg (B).exponent_pos.le zero_le_one) (fun i U j=> by obtain ⟨v,h,_⟩:=hv.gas.bought; exact live H x M a' i U (((h i).works U).choose_spec))).buyer
   refine ⟨_,_,hR.shrink ?_ hA hb,hX,hb',hP',he',hZ',hW'⟩
   linarith only [he,hk.allow]
end YM.PhysicalNext.Repeat.Mallow.Many
