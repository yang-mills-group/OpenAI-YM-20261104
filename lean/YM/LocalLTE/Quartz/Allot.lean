import YM.LocalLTE.Marked.Flint
import YM.MergeProof.Emit
/-! # Regular script for second unforced log. Keeps repeats. No Hessian subtraction yet!

Anchor on UNION site; pays factor exp surplus at endpoint, doesn't move
 each genealogy to fresh center. Keep honest clustered labels.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.March
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained Gas Ursell
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {I : Finset (Tubular f G)} {η r q a Y W d C' A b s μ C v B: ℝ} {Ñ : ChartRatio G}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R} {Ξ : Utopia H j v d r C' χ}
open Next.Foundations

open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt

namespace Captain
variable (N : Captain H j C' d v Y A b r B q k χ)
variable (p : Clusters H.ThinP)
open Greenbelt


open Merge Merge.Palette Height Daisy Lotus
-- every factor still selected independently.R.indices attached later. purposes geometry active.Down.
variable {ι:Type}[Fintype ι] (M:ι→Lotus.Leaf R)(rA:ι→ℝ)(he:∀ i, 0≤rA i)
set_option quotPrecheck false
local notation "χz"=> Merge.Palette.sign M S
local notation "τ"=> Merge.Tickets (Merge.Palette.sign M S)

-- bet costs on multiselects and draw routes. Prove zero off.R.
-- TERR Bayesian.
variable (D:Oscars M p)include N
local notation "P'"=> wingTerm (χ:=χ) p M D
variable (h':HostQ H N.conduit A B k)
-- amplitude.Bank
include h'
omit [Fintype ι] in
lemma burnt (Z:BudgetPoint)(ht:Z.threshold=Pressure.temp s):
    ∀ V, Healthy Z.threshold (reachability (H:=H) p) V→ Ore V (wingTerm (χ:=χ) p M D) v (wingBill N p M D) j :=by
    let X:=reachability (H:=H) p; let f i:= waltz H χ M (p.2 i) (D i); let Y i := H.smallAt (p.2 i); let a:=coefficient H.seam p.2 /↑(p.fst+1).factorial
    let g i:=inlet N M (p.2 i).val (D i); have hv i: 0≤g i:=inlet_nn N M (D i) _
    have h i V:= vivid N M V (D i) (p.2 i) h'
    have hl U:P' U=a*∏ i,f i U:=by unfold wingTerm a f; ring
    have hY i: Y i ⊆ X:= subset_biUnion_of_mem (H.smallAt ∘ p.2) (mem_univ _)
    have hF V (hV:Healthy Z.threshold X V): Ore V P' v (wingBill N p M D) j := by
       intro E _ _ _ U x he hB
       rw [ht] at hV
       have hh := Brush.all_prod univ (fun i t=> f i (U t)) g (fun _=>1) (fun i _=> ((h i V).2.2.2.2 (Finset.disjoint_of_subset_left (hY i) hV)) E U x he hB)
       simp_rw [Function.comp_def,hl]; apply (hh.trim.smul a).climb _ le_rfl
       simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_option,Fintype.card_fin,mul_one]
       unfold wingBill; let e:= coefficient H.seam p.2;change ‖a‖*((∏ i,g i)*(1+((p.fst+1:ℕ):ℝ))^j) ≤ |e| *(∏ i,2^j*g i)/_
       conv_rhs => rw [prod_mul_distrib,Finset.prod_const,card_univ,Fintype.card_option,Fintype.card_fin]
       have he : (1+((p.fst+1:ℕ):ℝ))^j ≤ (2^j : ℝ)^(p.fst+1) := by
          rw [← pow_mul,Nat.mul_comm,pow_mul]; gcongr; rw [add_comm]; exact_mod_cast Nat.lt_two_pow_self (n:=p.fst+1)
       apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (Finset.prod_nonneg fun i _=>hv i)) (norm_nonneg a)).trans_eq
       unfold a e; rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (by positivity : 0 ≤ ((p.1+1).factorial:ℝ))]; ring
    exact hF
end Captain
end YM.ConnectedActivityE6.Blaze.March
