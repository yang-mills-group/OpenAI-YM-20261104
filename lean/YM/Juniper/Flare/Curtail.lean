import YM.Juniper.Flare.Canvas
/-! # Regrouping aid. A family of CURTAIN pre-reprojection symbols pays
      its statements in its own valuation gauge. Bring this into panel with
      newly charged (template) soft books: carry all flags and real masks!
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Flare.Curtain
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Rain Roost
open Progress.DirectedRecipe Time Refrain Bright
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {c : Side} {i j k b w D m : ℕ} {Z : Stars→ Side}
variable {a W : ℝ}
variable {P:BudgetPoint}
variable (T:Curtain G c) (Q:∀ i:Stars,Curtain G (Z i))(hp:∀ i:Stars,(Z i).val=2*(w+i.val))
local notation "A" => (T.book.read T.stamp)
local notation "g" => (fun i=>(Q i).root)
-- Reach / reference oriented.
variable (P)
def faint (D:ℕ) (j:Site c) (Y:Config G c) := T.maskedRoot P j Y-T.root j 1-Trio.unearned P hp D (Trio.rip (fun i x=>(Q i).root x)) j Y
local notation "f"=> faint P T Q hp D -- implicit argument order?
variable {P T Q} (h:T.TidyC P m a) (hQ:∀ i:Stars,(Q i).TidyC P m a)
local notation "Q₁"=> Trio.ornament (c:=c) hp g
local notation "Θ"=> ∑ i:Stars,|Slide.ray i| *((Fintype.card (Site (Z i)):ℝ)*(a+a))
include T Q hp h
lemma sits (V:Config G c) : (A).additive P V= (Fintype.card (Site c):ℝ)*T.root 0 1+ (∑ i:Site c, masked P.threshold (neighbors D i) (Q₁ i) V)+ ∑ i:Site c,f i V:= by
   have he i:T.root i 1=T.root 0 1:= by
      simpa [Lattice.affine,VerifiedReset.pull_one_field] using (Curtain.mirrors h 0 1 i (1:Config G c)).symm
   rw [liberal]; unfold Trio.ornament; rw [Trio.parade]; unfold faint; simp_rw [he]; rw [sum_sub_distrib,sum_sub_distrib,sum_const,nsmul_eq_mul,card_univ]; ring
omit h T Q hp in
lemma Tidy.grow {V Q : Support c}{u:Config G c→ℝ} (h: Tidy P V u) (he: V⊆Q): Tidy P Q u:= {h with uses:= fun x y hh hp=> h.uses x y (agrees_mono hh he) (by rw [←inter_eq_left.mpr he, Finset.inter_assoc,hp, ←inter_assoc]) }
-- grow lemma should omit vars
include hQ
lemma coherence (hC: CompatibleP P m T.root (fun i=> (Q i).root))(hm:0 < m) (hl:2*m≤w)(hh:w+4 ≤ D)(ht: 4*m+16 ≤ c.val) : Voucher.LightTax P (2*D) (faint P T Q hp D) (a+a+Θ):= by
   have h₁ (i:Site c): neighbors m i⊆ neighbors (2*D) i:= fun j hj => (neighbors_mem ..).mpr (((neighbors_mem ..).1 hj).trans (by omega))
   constructor
   · intro i
     refine Trio.tidy_sub P (u:=T.maskedRoot P i - (fun _=>T.root i 1)) (v:=fun x=> Trio.unearned P hp D (rip g) i x) ?_ ?_
     · exact Trio.tidy_sub _ (Tidy.grow (shape h i) (h₁ _)) (tidy_const P _)
     exact Trio.tidy_sum _ _ _ _ fun j _=> Trio.tidy_scale _ _ (Trio.tidy_sum _ _ _ _ fun z _=> Trio.tidy_mask _ (unit_m P hp D g (fun i k=> CouplingShape.reg_extend (Curtain.pose (hQ _) k) (subset_univ _)) hh (Trio.emerge hp j z i) j z) (Trio.patch hp D hh j z i le_rfl))
   · intro i V hV; unfold faint; rw [Curtain.masked_root h i V (hV.mono_left (h₁ i))]
     exact sub_eq_zero.mpr (Trio.cruising P hp D (rip g) V i hh hl le_rfl ht hV _ (Trio.tinted T.root g hC) hm).symm
   intro i V; unfold faint; refine (norm_sub_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add (Curtain.life h i V) (Curtain.primeC h i 1 (UVNext.CouplingReset.flags_one P)))) (Trio.stipends P V hp D g (fun _=>a) (fun i z he j=> Curtain.primeC (hQ i) j _ he) hh i))
end YM.Juniper.Flare.Curtain
