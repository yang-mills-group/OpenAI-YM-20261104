import YM.OPE.Compatible.Month.Goblin
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Null
/-!
# Sparse true ballots in local reports on all-lit standby wind. Smooth exponent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open AnalyticBridge.VerifiedReset
open Next.Rank.Thirst
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : Rep G f}
    {p : BudgetPoint} {m n: ℕ} {W a r t σ E Λ μ x κ C w ε D b B: ℝ} {Ñ:ChartRatio G}
variable {F:Forest S.ratio} {I J:Seats F}{X Y Z:Support f}{q:Support c}
lemma cleared_v (U:F.Slice G)(hf:0≤r)(ht:4*r≤ B)(h: lights univ U r) : RG.flags B (F.drape U)=∅:=Finset.eq_empty_iff_forall_notMem.mpr (fun i hi=>by
       obtain ⟨p,hp,he⟩:= (RG.flags_spec ..).1 hi; refine not_le.mpr he ((shutterCh p _ r (fun x _ _=>?_)).trans ht); by_cases he:x∈ F.trunks
       · rw [F.on_tree U ⟨x,he⟩]; rwa [G.chord_one]
       let u:F.Free:=⟨x,he⟩; rw [show F.drape U x=_ from F.off_tree U u]; exact h u (mem_univ _))
def Bravo (R:Rep G f)(V:Config G c)(k:S.Choices)(U:Config G f):= R.beta*(mainTerm R.clip R.path U+ noiseTaylor S V U k) + Precision.loop R.path U
def RockV (R:Rep G f)(m:ℕ)(J:Seats F)(U:Config G f):ℝ:= cinnamon R m J U - tweak J (R.activities.additive R.p) U
lemma rockP (U:F.Slice G)(hf:0≤r)(ht:4*r≤ R.p.threshold)(hl: lights univ U r)(Z:FoldsGrip F I X)(hk:m≤R.p.B)(h:R.Lawful σ C Λ E w)(hc:WilsonStartup.Decent R.clip R.p)(hy:Geo.Width R.p R.clip σ) (V:Config G c)(k:S.Choices) :
    Ruin R V m I k (F.drape U)= Real.exp (-(tweak I (Bravo R V k) (F.drape U))) * Real.exp (RockV R m I (F.drape U)):=by
          let y:= F.drape U; let z:=razed I y; let v:=Real.exp
          have hY:RG.flags R.p.threshold y=∅:=cleared_v U hf ht hl; have hZ:RG.flags R.p.threshold z=∅:=by unfold z y;rw [draped]; exact cleared_v _ hf ht (Primacy.glints U hf hl)
          have he:= expr h hc hy Z (subset_univ _) hk y (show Healthy R.p.threshold univ y by unfold Healthy; rw [hY];simp) (show Healthy R.p.threshold univ z by unfold Healthy; rw [hZ];simp)
          have hp:= Pane.crystalline R.path R.clip R.p R.beta _ hY; have hx:= Pane.crystalline R.path R.clip R.p R.beta _ hZ -- implicit dots check
          change Ruin _ _ _ _ _ y= Real.exp _ * _; rw [Ruin,← Real.exp_add,← Real.exp_add,← he]; apply congr_arg Real.exp
          unfold RockV tweak; change (R.exponent y-R.exponent z+cinnamon R m I y)+ -(R.beta*noiseTaylor S V y k- R.beta*noiseTaylor S V z k)= -(Bravo R V k y-Bravo R V k z) + (cinnamon R m I y- (R.activities.additive R.p y-R.activities.additive R.p z))
          unfold Rep.exponent Bravo; rw [hp,hx]; ring
abbrev Arbor (V:Config G c)(R:Rep G f)(k:S.Choices)(I J:Seats F)(B:ℝ)(x:World F J G)(p:World F I G) := if Shelter I B p then Real.exp (-(tweak I (Bravo R V k) (F.drape (Wind I p (ald I J x))))) else 0
lemma litA (x:World F J G)(H:I⊆J)(ht:a ≤ B)(hf:0 ≤ B)(hp:dazed H a B x)(p:World F I G)(hu:Shelter I B p): lights univ (Wind I p (ald I J x)) B:=by
     intro u _; let z:=ald I J x; by_cases hx:u ∈ I
     · rw [show Wind I p z u=p _ from congr_fun (interior_e I p z) ⟨u,hx⟩];exact hu _
     rw [show Wind I p z u=z _ from exterior_e I p z ⟨u,hx⟩]; unfold z ald; dsimp only; split
     next h=> exact (hp.2 _ hx).trans ht
     rwa [G.chord_one]
lemma olympia (U: World F J G)(R:Rep G f)(H:I⊆J)(V:Config G c)(k:S.Choices)(ht:a≤B)(hz:0≤ B)(hf:4*B≤ R.p.threshold)(hp:dazed H a B U)(Z:FoldsGrip F I X)(hk:m≤R.p.B)(h:R.Lawful σ C Λ E w)(hc:WilsonStartup.Decent R.clip R.p)(hy:Geo.Width R.p R.clip σ) (p:World F I G): ballotY I R V m k B U p= Arbor V R k I J B U p * Real.exp (RockV R m I (F.drape (Wind I p (ald I J U)))):=by
          unfold ballotY Arbor; split_ifs with hX; exact rockP _ hz hf (litA U H ht hz hp p hX) Z hk h hc hy _ _; rw [zero_mul]
end YM.PhysicalNext.Repeat.Aroma
