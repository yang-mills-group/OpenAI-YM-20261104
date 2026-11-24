import YM.Integration.WilsonIndependentSpoutPhysicalOrbit
import YM.SignedWilsonExpansion.Purchase.Junior
/-! # Opening on the auxiliary clock/order roster

 Uses the actual nested-length original course and InfraredAtlas elections, one threshold for all rows
 (colors chosen once); not declaring a comparison for arbitrary spheres. All p-conditions of the issued
 physical-prefix horizon cover *whole product* & proper faces. Pre-cost `Requested` needed on this run.
 Report cost carried through Birth on the same chart, through *complete* journey to `finallyW`. Here
 top spacing matches actual ruler (not powers-of-three assumed on regulator step length) with the final
 inference stop of the order-two comparison taken inside later. Bare stencil limits not taken here.
-/
set_option autoImplicit false
set_option maxHeartbeats 789000
noncomputable section
namespace YM.SignedWilsonExpansion.Fire.EraU
open XSpace Precision Wilson Gauge RG Source Labels Lattice PertExtension
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa WilsonCoeffUV.Power WilsonCoeffUV.Cosmos
open Set Filter Function Asymptotics Integration PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Next.Foundations
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Atlas RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.Halo RegulatorIR.Gain RegulatorIR.Epoch RegulatorIR.Calibration
open RegulatorIR.Ledger.Sky RegulatorIR.Prim RegulatorIR.Cluster RegulatorIR.Clocks RegulatorIR.Budget RegulatorIR.Budget.Layer RegulatorIR.Profiles RegulatorIR.Budget.Packet RegulatorIR.Geometry
open Purchases Purchases.HalfRoof Purchases.HalfRoof.Cooking
open WilsonOriginalPublicNodalPhysicalMerBook (Issued)
open WilsonIndependentSpoutOriginalMarkedJourney (source)
open Reef
open scoped Topology Classical NNReal ENNReal BigOperators
variable {G:Gauge}{I J:Type}(R:PhysicalNext.Repeat.Legato.Run G)
variable {p:ℕ}
-- Generic enlisted marked vertex
section reports
variable {M:J→ℕ}{sid:Page M→Side}{K:KernelChoices} (C:Oracle.Circuit M sid)(Y:Program K)
    (Z:∀P:Patch,P.Branches K G)(F:Tent M)(A:J→Levels G)(s:J→ℕ)(Ñ:ChartRatio G)(V:I→Pill G)
    (arm:Composite I)(site:J→I→ Cover)
local notation "W" => (fun w=> Reef.welcome V (site w) arm)
local notation "paid" => Reef.Ear.report V arm (C.payroll Y G Z (sheet F)) site
open WilsonIndependentNotebookPayrollMark in
lemma lather (w:J): Reef.seed V (site w) arm=WilsonIndependentNotebookPayrollMark.source A s (Page.opening M w) (W w):=by
   have hu:= Reef.kinetic V (site w) arm; have hv:= Reef.composed V (site w) arm
   exact WilsonIndependentMatchedOpeningCover.source _ _ (WilsonIndependentMatchedOpeningCover.recover _ _ hu hv.1.canopy hv.1.symmetry hv.2 (fun n y=> Reef.minded V (site w) arm y)) A s w

def journey (v:J):= cruises (A v) Ñ (s v+M v) (Reef.homeRank V arm) (s v+ M v) (s v) (W v) -- explicit M
local notation "P₀" => (journey (M:=M) A s Ñ V arm site)
lemma recieved (simple:G.Simple)(green:LocalRatio Ñ)(v:J)(read:∀f,WilsonIndependentNotebookMarkedEdge.Reads C Y Z F A s p f):
    Clocks.Matches p ((paid).main (Page.finallyW M v)) (source A s Ñ (Page.finallyW M v) (P₀ v)):=by
   have hu:= Reef.kinetic V (site v) arm
   have e:Clocks.Matches p ((paid).main (Page.opening M v)) (source A s Ñ (Page.opening M v) (W v)):=by
      rw [WilsonIndependentSpoutOriginalMarkedJourney.entry A s Ñ green]; intro i hi
      exact congr_fun ( lather (M:=M) A s V arm site v) i
   have ht:=WilsonIndependentSpoutOriginalMarkedJourney.original C Y Z F A s p read simple Ñ green (Reef.homeRank V arm) paid v 0 (Nat.zero_le _) (W v) hu e (M v) (Nat.zero_le _) le_rfl
   change Clocks.Matches p ((paid).main (Page.finallyW M v)) (source A s Ñ (Page.finallyW M v) (cruises (A v) Ñ (s v+M v) _ (s v+(M v-0)) (s v+(M v-M v)) (W v))) at ht
   simpa only [journey,Nat.sub_zero,Nat.sub_self,Nat.add_zero] using ht
open WilsonIndependentSpoutScalarLedger (scalar)
open PowerSeries
lemma clocked (v:J): scalar ( source A s Ñ (Page.finallyW M v) (P₀ v) )=rear (A v) Ñ (s v+M v) (s v) (s v+M v) (dew (P₀ v)):=by
    rw [WilsonIndependentSpoutScalarLedger.reported]; change Bank.reel (relativeC (A v) Ñ (s v+M v) (s v+(M v-M v)) (M v)) (dew (P₀ v))= _; unfold rear; congr <;> simp
lemma cooled (v:J)(simple:G.Simple)(green:LocalRatio Ñ) (read:∀f,WilsonIndependentNotebookMarkedEdge.Reads C Y Z F A s p f)(q:ℕ)(hp:q≤p):
    note ((paid).main (Page.finallyW M v) q 0) = coeff q (rear (A v) Ñ (s v+M v) (s v) (s v+M v) (FadeRaw (A v) Ñ (s v+M v) (Reef.homeRank V arm) (s v) (s v+M v) (W v))) := by
    have he:= recieved C Y Z F A s Ñ V arm site simple green v read
    change note _= coeff q (rear _ _ _ _ _ (dew (P₀ v))); rw [←clocked, WilsonIndependentSpoutScalarLedger.scalar,coeff_mk]; rw [he q hp]
end reports
open WilsonPositionProgramInfraredCircuit
section arithmetic
abbrev setting: XSpace.Run:=⟨3,by decide,1, finalP,by decide,by decide⟩
local notation "A"=> R.family.path.levels
open WilsonPositionProgramNestedElection (course)
lemma titleP {simple:G.Simple}{a:Axis}{ε:ℝ}(p:course simple a ε R.kit): ∃ v:ℕ→ℕ,∀ n,((A).S.block n).val=(3:ℕ)^ (v n) := by
    obtain ⟨v,_,p⟩:= p.2.1
    refine ⟨fun n=>(v ((A).clock.J (n+1))).factorial,fun n=> ?_⟩
    have hx:((A).S.block n)=R.rolls.L ((A).clock.J (n+1)):= Push.PriceCompiler.block_eq R.alloy.B.valid n
    rw [hx, (p _).2]; rfl
variable (m j w:I→ℕ) (v:I→ℕ→ℕ) 
open WilsonPositionProgramCommonWindow 
lemma width_grow (s:∀ i n,((A).S.block (m i+n)).val=setting.ratio^(v i n))(i:I)(d:ℕ): gainB (A).S (m i) d= setting.ratio^(elapsed (v i) d):=by
    induction d with | zero=> simp [gainB,WilsonPositionProgramCommonWindow.elapsed] | succ d ih=> rw [gain_step, ih,s,show elapsed (v i) (d+1)=_+v i d from Finset.sum_range_succ .., pow_add]; rfl
lemma range_age (s:∀ i n,((A).S.block (m i+n)).val=setting.ratio^(v i n))(i:I): count setting j v (Page.opening j i)=(orbitP (A).S (m i) (m i+j i)).side:=by
    apply Subtype.ext; change 16*setting.ratio^(elapsed (v i) (j i-0))=16*gainB (A).S (m i) (m i+j i-m i); rw [width_grow R m v s, Nat.sub_zero, Nat.add_sub_cancel_left] -- count.of
open WilsonPositionProgramInfraredMeter in
lemma money (s:∀ i n,((A).S.block (m i+n)).val=setting.ratio^(v i n))(t:ℝ)(i:I): amount R setting m j v w t i= amountV A m (m+j) t w i:=by
    unfold WilsonPositionProgramInfraredMeter.amount amountV; rw [range_age R m j v s i]; simp only [widthY,RG16.Lambda,Pi.add_apply,XSpace.Run.step,XSpace.Run.den,setting, Nat.cast_pow,Nat.cast_ofNat, div_inv_eq_mul]
end arithmetic

section fire
variable (W:Initialize G)(Z:∀P:Patch,P.Branches R.family.path.levels.clock.kernel G)(m j:I→ℕ)(v:I→ℕ→ℕ)(ρ:I→ℝ)(r:∀ i,0<ρ i)
local notation "C"=> R.family
local notation "A"=> R.family.path.levels
local notation "Ñ"=> R.metals.O
abbrev meshFi (i:I):= roof A (m i) (m i+j i) (ρ i) (r i)
local notation "F"=> meshFi R m j ρ r
open WilsonPositionProgramSubmittedGeometry (center)
open PowerSeries
lemma provision {T:Tent j}(simple:G.Simple)(s:∀ i n,((A).S.block (m i+n)).val=setting.ratio^(v i n))(issued:Issued R setting m j v s Z p T)
    {n:ℕ}(V:Fin (n+1)→Pill G)(site:I→Fin (n+1) → Cover)(ip:I→ℕ)(H:ℝ) (wage:MeterD A ρ r m (m+j) H site ip)(q:ℕ)(hp:q≤p):
    ∃D:ℝ,∃k:ℕ,0≤D∧∀ i, ‖coeff q ( normalizedInsertionSeries V (site i) (F i) W )- coeff q (initialClock A Ñ (m i) (m i+j i) V (site i))‖ ≤ D *amountV A m (m+j) H ip i ^ k*(widthY A m (m+j) i)^(-(1/4:ℝ)):=by
    let F':= F; let Ć:=WilsonPositionProgramInfraredCircuit.circuit R setting m j v s
    let Y:= Oracle.books (A).clock.kernel; let L:= WilsonPositionProgramInfraredMeter.wallet R setting m j v ip H
    let S:= Ć.dialect Y G Z (sheet T); let x:= fun i=>center (F' i) (lumber (F' i)); have scale (i:I): (count setting j v (Page.opening j i))= (F' i).p.side:= range_age R m j v s i
    have safe:S.cushion (1/8) x:=by intro u; have hu:= WilsonPositionProgramSubmittedGeometry.pin (F' u) (lumber (F' u)) ( HalfRoof.position _ ); rw [← scale] at hu; exact hu
    have debt (i:I): ENNReal.ofReal (1+Reef.Ear.span (x i) (site i) (wholeP n))≤L.val i:= by
        apply ENNReal.ofReal_le_ofReal; change _≤ WilsonPositionProgramInfraredMeter.amount R setting m j v ip H i; rw [money R m j ip v s]; exact wage i
    obtain ⟨cash,lamp,ending⟩:= issued.funded ip H
    obtain ⟨unit,D,hd⟩:= units R setting m j v s
    obtain ⟨H₀,k,h,estimate⟩:= Reef.Ear.terminal V (wholeP n) site cash lamp ending (fun i=> (F' i).p) (fun i=> W.tree _) x unit issued.flat scale debt (show 0<(1/8:ℝ) by norm_num) safe q hp (by norm_num) D hd
    refine ⟨H₀,k,h,fun i=>?_⟩
    have price:= estimate i
    rw [cooled Ć Y Z T (fun _=> A) m Ñ V (wholeP n) site i simple (RunFormalChain.fromRun R).receipt issued.marked q hp] at price
    let χ :ℝ:= WilsonPositionProgramInfraredMeter.amount R setting m j v ip H i; have ht : L.val i= ENNReal.ofReal χ := rfl
    have hx: (L.val i).toReal= amountV A m (m+j) H ip i:=by rw [ht, ENNReal.toReal_ofReal (zero_le_one.trans (WilsonPositionProgramInfraredMeter.lower R ..) : 0≤χ)]; exact money R m j ip v s H i
    -- unify age to lamp (Π fence)
    let U:= Ć.lane Y G Z (sheet T); let β:= rear A Ñ (m i+j i) (m i) (m i+j i); let Θ:= FadeRaw A Ñ (m i+j i) ( Reef.homeRank V (wholeP n) ) (m i) (m i+j i) (Reef.welcome V (site i) (wholeP n));
    have hP: S.P i=(widthY A m (m+j) i):=by change ((count setting j v (Page.opening j i)).val:ℝ)=_; rw [scale]; rfl
    change ‖coeff q ( normalizedInsertionSeries V (site i) (F' i) W)- (↑(coeff q (β Θ)):ℂ)‖≤H₀ * (L.val i).toReal^k * (S.P i)^(-((1/2:ℝ)/2)) at price
    rw [initialClock, insertQ,coeff_map]; rw [hx,hP,show -((1/2:ℝ)/2)=-(1/4:ℝ) from by norm_num] at price
    exact price
open WilsonPositionProgramNestedElection (course)
include Z
lemma insured (col:G.ColorIndex) {a:Axis}{ε:ℝ}(simple:G.Simple)
    (c:course simple a ε R.kit)(g:WilsonPositionProgramStageInvoice.Requested R.kit)(b:WilsonWindowReportingPace.Slow R.kit):
    ∃start:ℕ,Campfire I G p A Ñ W start:=by
    obtain ⟨base,sale⟩:= WilsonOriginalPublicNodalPhysicalMerBook.original (X:=I) R setting Z col simple p c g b
    obtain ⟨u,hu⟩:= titleP R c
    refine ⟨base,⟨?_⟩⟩
    intro n V l c pQ h old pLine site x t meter q hp
    let j':= c-l; let v':=fun (i:I) (n:ℕ)=> u (l i+n)
    have s:∀ i n,((A).S.block (l i+n)).val=setting.ratio^(v' i n):=fun i n=> hu _
    have hw: c=l+j':=funext fun i=> (Nat.add_sub_of_le (pLine i)).symm
    obtain ⟨F',issued⟩:= sale l j' v' s old
    have trip:= provision R W Z l j' v' pQ h simple s issued V site x t (hw ▸ meter) q hp
    obtain ⟨C',k,hn,trip⟩:= trip
    refine ⟨C',k,hn,fun i=>?_⟩; rw [hw]; exact trip i
end fire
end YM.SignedWilsonExpansion.Fire.EraU
