import YM.OPE.Compatible.Juniper.Laid
/-!
# Ink equality all tapes. tested mode off R
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{C:KernelChoices}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin
local notation "Fλ"=> fieldX (Shade G)
abbrev orbitU (b:ℕ)(x:Fλ)(t:ℝ):= Exposure b (t⁻¹ • board (lotU (t • x)))
noncomputable abbrev Autum (p:Scoop G b→ℝ)(x:Fλ): JetS ℝ:= Jpiece (BFilm b x) p
noncomputable def AuroraK (b:ℕ)(x:Fλ):= magnol G 4*RoadK b^4*(1+‖InLine (4*b) x‖)^4
lemma aurora_non (b:ℕ)(x:Fλ):0 ≤ AuroraK b x:= by unfold AuroraK; have he: 0≤ magnol G 4:=(ozone G 1 1 _ zero_le_one (lumenD G) 4).choose_spec.1; positivity
def Oxone (t b C:ℝ):= C*b + (Nat.factorial 3:ℝ)*C*(3*t)^3
lemma auroraPay (p:Scoop G b→ℝ)(x:Fλ)(C R:ℝ)(hC:0≤ C)(h:ContDiff ℝ 3 p)(hp:TagN (BFilm b x)+AuroraK b x≤ R)(hq:∀ i:ℕ,i ≤ 3→∀ y:Scoop G b, ‖y‖≤R→ ‖iteratedFDeriv ℝ i p y‖ ≤ C)(t:ℝ)(ht:0<t)(hV:t≤1):
       ‖p (orbitU b x t)-(Autum p x).atK t‖ ≤ Oxone (TagN (BFilm b x)) (AuroraK b x) C * t^3:= Flare _ _ R _ h hp (aurora_non ..) hC hq _ _ ht hV (borax b x ht)
lemma auroraΨ (p:Scoop G b→ℝ)(x:Fλ)(h:ContDiff ℝ 3 p): Libra.Reads (p ∘ orbitU b x) (Autum p x):=by
       let a:=BFilm b x; let V:=TagN a; let B:= AuroraK b x; obtain ⟨K,hK,H⟩:= grabK p 3 (by exact_mod_cast h) (V+B); unfold Libra.Reads; refine Asymptotics.isBigO_iff.mpr ⟨Oxone V B K,?_⟩; filter_upwards [Tested.eventually_small one_pos] with t ht; rw [Real.norm_of_nonneg (show 0≤ gradeP 3 t from pow_nonneg ht.1.le _)]; exact auroraPay p x K _ (zero_le_one.trans hK) h le_rfl H t ht.1 ht.2.le
lemma upTest (p:Pole (Scoop G b) i)(U:CoverConfig G): testQ (Honey (Soul p)) U= p (fun _=> Exposure b (board U)):=by
       let k:= Honey (Soul p); let t:= board U
       calc
          _=wholeX k (fun _=>t) := tsum_congr fun i=> congr_arg (fun w=>k i*w) (issue i U).symm
          _= _:=(dropK (Soul p) (fun _=>t)).trans (by change p _=p _; congr 1; funext i; change Packer G b (Exposure _ t)=_; rw[Fort]; apply congr_arg; funext j; change royal j.val t=indexS _ _; rw [champ,show risingO t=t from by simpa only[one_smul] using sourceU U 1])
lemma froX (z:ℝ)(p:Pole (Scoop G b) i)(U:CoverConfig G): p (fun _=> Exposure b (z⁻¹ • board U))=(z^i)⁻¹*testQ (Honey (Soul p)) U:=by rw[upTest, show Exposure b _= z⁻¹ • Exposure b (board U) from by unfold Exposure; rw [map_smul,map_smul],p.map_smul_univ (fun _=>z⁻¹) (fun _=>Exposure b (board U))]; simp [smul_eq_mul]
variable (v:Bid.Dir G n) {p:Song (Scoop G b)} (H:ReadyP p k)
open Arc Stranded Adhesion
local notation "χ"=> Script.value
lemma Boast (p:Pole (Scoop G b) i)(hp:i≤k): Libra.Reads (Tensor.diagonal p ∘ orbitU b (charW o v)) (inkM (Grid.lance (Honey (Soul p))) k o v):=by
      have he:= Grid.nestsL (d:=k) (crownG (Soul p) (2*(i+2))) hp le_rfl (fun _=>v) (show Gael (fun _=>v) from ⟨_,Reads.constants _⟩) o; unfold Libra.Reads; refine he.congr' ?_ Filter.EventuallyEq.rfl; filter_upwards with t; congr 1; apply Eq.symm; change p (fun _=> Exposure b (t⁻¹ • board (lotU (t • _))))= (t^i)⁻¹ * _; rw[froX,show lotU (t • charW o v)= _ from (show lotU (t • charW o v)=expandAt o (represent (t • v)) from by rw [← Grid.plank, map_smul];rfl)] -- cong shape ambiguity
lemma silk2 (X:Finset F)(p:F→ℝ→ℝ)(v:F→Token)(h:∀ i∈X,Libra.Reads (p i) (v i)): Libra.Reads (∑ i∈X,p i) (∑ i∈X,v i):=by
      induction X using Finset.induction_on with
      | empty=> exact by simpa only [Finset.sum_empty] using! Reads.constants (0:ℝ)
      | insert i s hi ih=> rw[sum_insert hi,sum_insert hi]; exact Reads.sum (h i (mem_insert_self ..)) (ih fun j hj=> h j (mem_insert_of_mem hj))
lemma radiates {τ:Phase→ℕ}(H':Aware k τ) : inkM (Drift.spread G k τ (ChiselV H' H).val) k o v= Autum (Strike k p) (charW o v):=by
       rw [Weft H' H]; refine Reads.equality ?_ (auroraΨ _ _ ((sailCost p k).cost.smooth.of_le le_top)); let Yz (i:Fin (k+1)):= Grid.lance (ShapeX p i.val); choose U hz h using fun i:Fin (k+1)=> Grid.crib G _ _ (2*(i.val+2)) 0 (Nat.le_of_lt_succ i.isLt) (show 0+2*(i.val+2)≤2*(i.val+2) from by simp); let B(i:Fin (k+1)):= U i*(gumBill G (4*b) i.val (2*(i.val+2))*‖Soul (p i.val)‖); change Libra.Reads _ (inkM (∑ i,Yz i) k o v); rw [inkify v univ Yz B (fun i _=>h i _ _ (crownG ..))]; rw [show Strike k p ∘ orbitU b (charW o v)=(∑ i:Fin (k+1),Tensor.diagonal (p i.val) ∘ orbitU b (charW o v)) from ?_]; exact silk2 _ _ _ (fun i _=> Boast o v _ (Nat.le_of_lt_succ i.isLt))
       funext x; rw [Finset.sum_apply]; exact (Fin.sum_univ_eq_sum_range (fun i=> Tensor.diagonal (p i) _) _).symm -- param
end YM.OPE.Spells
