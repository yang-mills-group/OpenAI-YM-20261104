import YM.LocalLTE.Port.Dust
import YM.LocalLTE.Port.Shiny
/-! # root weights compression prior photo. Analyst keeps same carrier. Lantern.P returns plugs budgets.T.Certificate. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Set Lattice RG Pressure Wilson Finset MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus FrameBox Cabana Push
open Progress.DirectedRecipe MergeProof Menu Marker Accent Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge}{c f : Side}{Q : Rep G f} {S:StepData c f} {σ κ Λ μ' w t v : ℝ}
variable {V I J : Type}[DecidableEq V][Fintype V] {R:Marker.Census V}(B:Bands R Q)(r:V→ℝ) (hr:∀ i,0<r i) (o:V→Site f)
open Extra.Trajectories Next.Foundations
variable {d U:ℕ} {a₀ c₁ a β:ℝ}
local notation "P"=> Q.p
local notation "ν"=> Q.p.threshold
local notation "W₀"=> Config G f
variable (h:B.Active)(hw:B.Radial r a₀ a v c₁)
open Push.AbsoluteSums Push.AbsoluteSums.Animals
local notation "Θ"=> Outpost R f U
local notation "TP" => HarborP B U
local notation "TT"=> FamilyE B
variable (hc:Shine R B d U κ)
include hc h hw
local notation "W'"=> (1+(U:ℝ))^(Q.p.power*Q.p.order)
def turnQ (Ps:BudgetPoint) (U:ℕ)(V:Type)[Fintype V](a:ℝ):=2*((1+(U:ℝ))^(Ps.power*Ps.order)*(((Fintype.card V):ℝ)*a))
-- emit proof fields covers whole.M.W.Path.User. Power no M.GPIO mark other vacancies.R.
variable (hm:HasSlots Q.p Q.activities)(e:(HarborP B U) × Bool↪ℕ)
structure Beaut (A:J→Menu.Hat R Q) (m k:ℕ)(κ:ℝ)(p:J→ Config G f→ℝ) : Prop where
     leads j : Fan.Mind (A j).M (p j) κ m k
     price j i : (A j).M.turn=Wing.logKey i→(Q.activities.reg i).support ⊆ Animals.neighbors k (Q.activities.reg i).site
include hm
-- truly buys not invokes E.S.C.Fl Witness. Hearts.Controller.Bind.
lemma roses : ∃ (F:(HarborP B U) × Bool→ Menu.Hat R Q), (∀ i,(F i).M.turn=.logKey (blankRow f (pedestal B i.1,e i)))∧ PL B.origins F ∧ (∑ i, sumFee (F i) r*Q.p.mass (F i).M.crest (F i).M.weight) ≤ turnQ Q.p U V a ∧ (∃ u, Beaut F d U κ u)∧ ∀ x, roll F x=∑' j,B.ray j x :=by
    obtain ⟨Y,hY⟩:= Port.guideL B h hc
    obtain ⟨b,hb,hH⟩:= Port.axels B r h hw Y (fun i=> ⟨(hY i|>.1), (hY i|>.2.1)⟩)
    let n : ℝ:= (W'*(((Fintype.card V):ℝ)*a)); let X:= fun j: HarborP B U=> pedestal B j; let X' j:=(X j).support; let Ts(j:HarborP B U):= j.val.1.1
    let e':= cram Y b; have h₀(i):0≤b i:= ((hb i).1 false|>.2).1
    have h₁:Summable b:= Port.everyone r hw.pure Q.p X' Ts Y b hH h₀
    let f'(i: FamilyE B):= masked ν (B.support i.val) (B.H i.val)
    have ht(x): Summable fun i=> f' i x:=by
       refine (h₁.mul_left 2).of_norm_bounded (fun i=>?_)
       have hp:= (hb i).2; unfold f'; rw [(hY i).1]; by_cases he: Healthy ν ((X (Y i)).support) x
       · rw [masked_eq _ _ _ _ he]; exact hp.2 x he [] (by simp) (by simp)
       rw [masked_ne _ _ _ _ he,norm_zero]; exact hp.1
    let E(j:HarborP B U)(k)(x):= scaleQ k (cram Y (fun i=> f' i x) j)
    let hT(j:HarborP B U):= j.val.2.2.2.val; let f (j:HarborP B U):=j.val.2.2.1
    have h (j:TP) (k:Bool): ∃ ψ,Q.p.Regular (X' j) ψ ∧ Q.p.supBounds (X j).site (X' j) ψ (e' j) ∧ FrameBox.Polynomial (hT j) κ (j.val.2.1) d ψ ∧ E j k= masked ν (X' j) ψ:=by -- dummy
       let ξ:= X' j; let x':=(X j).site; let A:={i:FamilyE B// Y i=j}; let f0(i:A): W₀→ℝ:= scaleQ k ∘ B.H (i.val.val); let y(i:A):= b i.val;
       have hp (i:A) : ∃ S, f0 i=polymer (f j) (hT j) (d+1) κ S∧ Q.p.Regular (X' j) (f0 i) ∧ Q.p.supBounds x' (X' j) (f0 i) (y i):=by
          obtain ⟨p,hP⟩:= hY i.val|>.2.2 k; obtain ⟨ha,hb⟩:= hb i.val|>.1 k; unfold x'; let i':=Y i.val
          rw [i.property] at ha hb
          replace hP:∃ S, f0 i=polymer (f (Y i.val)) (hT (Y i.val)) (d+1) κ S:=⟨p,hP⟩
          rw [i.property] at hP
          obtain ⟨p,hP⟩:=hP; exact ⟨p,hP,ha,hb⟩
       obtain ⟨g,hP,hw,H⟩:= themed ξ (f j) (hT j) (d+1) κ P x' f0 y (h₁.comp_injective Subtype.val_injective) hp
       let w : W₀ →ℝ:= polymer (f j) (hT j) (d+1) κ g
       refine ⟨w,hP,hw,⟨f j,g,rfl⟩,?_⟩
       funext z; unfold E cram; rw [ContinuousLinearMap.map_tsum]; swap; · exact (ht z).comp_injective Subtype.val_injective
       by_cases he : Healthy ν ξ z
       · rw [masked_eq _ _ _ _ he]; let u: WaysQ P G ξ x':=⟨(z,[]), he,Nat.zero_le _,by simp⟩; have hp(i:A): f' i.val z=B.H i.val.val z:=masked_eq _ _ _ _ ((show B.support (i.val.val)=X' j from ((hY i.val).1.trans (congr_arg X' i.property))).symm ▸ he) -- order
         simp_rw [fun i:A=> hp i]; exact (H u).tsum_eq
       rw [masked_ne _ _ _ _ he]; exact (tsum_congr (fun i:A=> show (scaleQ k (f' i.val z))=0 from (by
          have hh:B.support i.val.val= ξ:= ((hY i.val).1.trans (congr_arg X' i.property)); unfold f'; rw [masked_ne _ _ _ _ (fun h=> he (hh ▸ h)),map_zero]))).trans tsum_zero
    choose u hu hv hg hz using h
    have hr(k:TP):(Ts k).val.Nonempty ∧ (Ts k).val.image B.origins⊆ X' k:=⟨k.property.1,k.property.2.1⟩
    have ht' k i:Sale Q.p (X' k) (E k i) (e' k):=by rw [hz]; exact Port.supportQ _ _ (hu k i) (hv _ _)
    let F':= Port.lea B.origins X Ts e' hr E ht' hm e
    have hB := Port.joinsL B.origins X Ts e' hr E ht' hm e
    have hF(k i):= Port.birthZ Q R (X k) (e (k,i)) _ (Ts k) (hr k).1 (e' k) i r (ht' k i) hm
    refine ⟨F',fun i=>rfl, hB,?_, ⟨fun i=> u i.1 i.2, ⟨fun i=>?_,fun i l h=> ?_⟩⟩,fun x=> ?_⟩
    · unfold turnQ F'; rw [prices r B.origins X Ts (cram Y b) hr E ht' hm e (e') (fun i=>rfl)]; exact mul_le_mul_of_nonneg_left (Port.wholeQ r Q.p X' Ts Y b hH) zero_le_two
    · let z:=X i.1; let t:= (F' i).M; have hx:t.crest=z.support:= ((hF i.1 i.2).2.1); let i':=blankRow _ (z,e i)
      refine ⟨⟨_,show t.turn=.logKey i' from rfl⟩,?_,⟨i',show t.turn=.logKey i' from rfl,?_,?_,?_⟩⟩
      · change E _ _= RG.masked _ t.crest _; rw [hx];exact hz ..
      · change (P).supBounds _ t.crest _ _; rw [hx,show Q.activities.reg i'=_ from Port.blanked hm _ _]; exact hv ..
      · change (P).Regular t.crest _;rw [hx]; exact hu ..
      rw [show Q.activities.reg i'=_ from Port.blanked hm _ _]; exact ⟨hT i.1, Nat.le_of_lt_succ i.1.val.2.2.2.prop,hg _ _⟩
    · rw [← show blankRow _ _ = l from Wing.logKey.inj (show (Wing.logKey (blankRow _ (X i.1,e i)))=.logKey l from h), Port.blanked hm ]; exact i.1.property.2.2.2
    unfold F'; rw [Port.mother _ X Ts _ _ E _ hm e Y f' ht (fun _ _ _=> rfl)];
    let s:FamilyE B ↪ ℕ:= ⟨Subtype.val,Subtype.val_injective⟩; refine Eq.symm (transferred_sum s ?_ ?_)
    · intro i; change B.ray i.val x= _; unfold Bands.ray; rw [(hY i).2.1]
    intro i hi; have hp:B.H i=0:= Classical.byContradiction fun h=>hi ⟨⟨i,h⟩,rfl⟩; unfold Bands.ray; rw [hp];by_cases hv: Healthy ν (B.support i) x; rw [masked_eq _ _ _ _ hv]; exact Poly.send_zero _; rw [masked_ne _ _ _ _ hv,Poly.send_zero]
end YM.LocalLTE.Port
