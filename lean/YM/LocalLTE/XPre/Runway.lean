import YM.LocalLTE.XPre.Bank
import YM.MergeProof.Wicket
import YM.MergeProof.South.Admit
/-!
# Pack *following* compression. Imperative bar unscaling overlaps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.XPre
open Function Finset Filter Set MeasureTheory Lattice Wilson RG
open Extra.Histories Push Local Motion Extra.Multi
open LocalLTE.Fan LocalLTE.River LocalLTE.Vinca Ticket
open PhysicalNext.Repeat Lotus Blush Progress.DirectedRecipe
open YM.MergeProof Menu Marker Accent Extra.Trajectories
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{c f:Side}{S:StepData c f} {R : Rep G f} {C: Rep G c}
variable {J I N T:Type}[DecidableEq J][Fintype J][Fintype I][Fintype N][Fintype T]
variable (B:Marker.Census J){d p m l K:ℕ} {κ V a t u v g s' :ℝ}
variable (A:T→Hat B R) (h:T→Prop)
variable (E:J→ Config G f→ℂ)(F:J→Res G f)(W:J→ Res G c)(v:J→ℂ) (w:J→ℝ) (hw:∀ i,0<w i)
variable (V:Support f→ Config G f→Poly B)(K₁:Box f→ Config G f→Poly B) (X: Config G f→Poly B)(H:GaugeDoor R C)(o:J→Site f)(ψ:J→ MergeProof.Response G c)
set_option quotPrecheck false
include hw
open LocalLTE.Port
lemma coast (hX:X= restore R E F V K₁)(ht:∀ U:Config G f, roll A U=Mach B (fun i=> E i U-v i)+ ∑ j,V j U)(hk:∀ i U,board A i U=Mach B (fun j=>F j i U)+K₁ i U) {t d:ℝ} (hs:R.Lawful s' a g t d) : ∀ U,X U= Poly.pass (Mach B v)*Expense (heap A) w S U:=by
   intro U; rw [hX,Expense,passIn (heap A) S hs hw U,golden,banded]
   have hP:(roll A U).part B.quiet=0:=by unfold roll; rw [Poly.part_sum]; exact Finset.sum_eq_zero (fun j _=> still A _ _)
   unfold restore; rw [mul_smul_comm,← mul_assoc, ← pass_add (mute B v) hP]; rw [ht]
   have ht: Mach B v+Mach B (fun i=> E i U-v i)=Mach B (fun i=> E i U):=by unfold Mach;rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _=>by rw [← Extra.Trajectories.send_add]; exact congr_arg (Poly.send _) (add_sub_cancel ..)
   rw [← add_assoc,ht];simp_rw [hk,add_assoc]; -- nested
omit hw
-- assembled. Has menu URI.Astral.Model Psi fixed. let future errors.next stage.
-- vacancy job mixed contributions chosen zero; truthful family columns at actual Birth.Prep.No projecting. log polynomial.
-- reusable cutter challenge:
variable (s0:ℝ)(t0 v0 y0:J→ℝ) (hg: ∀ i,∃ X:Set Wing,X.Finite ∧ LocalLTE.XPre.Circuit X H d κ p l (o i) (S.ratio.parent (o i)) 1 (E i) (F i) (W i) (v i) (t0 i) (v0 i) (y0 i))
variable (hs:SoundDoor S H)(hL:Tunes H)(hD:R.Lawful s' a g t u)
local notation "Xz"=> restore R E F (fun _ _=> (0:Poly B)) (fun _ _=>0)
local notation "bo"=> S.ratio.parent ∘ o
variable {cb β z:ℝ}
include hs hg hL hD hw
variable (hp:Fintype.card J ≤ K) (he:d≤ p) (hK:p ≤ m)(h':K*p ≤ m)(hκ:K≤ m)(hx:1≤ cb) (hY:J→ℝ)(hy:∀ i,0<hY i)(hγ:∀ i,w i*v0 i≤ z)
variable (hp0: (∑ j:J,w j*t0 j)+cb*(∑ j:J, 2*w j*(y0 j+hY j)) ≤ β)
include hp he hK h' hκ hx hy hγ hp0
-- Boom. heap century.Eta height power purchase.
lemma adornedL (R' : Config G f→Poly B) (hpQ:R'=Xz) : ∃ (I: Type)(_:Fintype I)(A:I→Hat B R)(φ:I→ Config G f→ℝ)(g':J→ MergeProof.Response G c)(F':I→Prop), (∀ i,(A i).s.val.image o⊆(A i).M.crest) ∧ (∀ i,F' i→ ProductInk (A i).M (φ i) κ m l ∧ ∀ j,(A i).M.turn=.logKey j → (R.activities.reg j).support⊆AbsoluteSums.Animals.neighbors l (R.activities.reg j).site) ∧ Accent.Garnish C.p (S.ratio.parent ∘ o) g' w (C.p.supportExponent+1) z ∧ (∀ i j U, (∑ a, owl (A a) H j i U)+hook C.activities C.p.threshold (g' j) i U=W j i U) ∧ (∀ U,R' U=Poly.pass (Mach B v)*Expense A w S U)∧ XPre.banks A F' cb w ≤ β+(Real.exp β -1) :=by
   obtain ⟨ψ,hψ,P,N,hP,hN,A,Zz ,X,hY1,hl,hk,hO,hv,hW⟩:= rally B E F W v w hw H o (S.ratio.parent ∘ o) t0 v0 y0 hg hs hL hY hy -- parse
   let M:= Sum.elim A Zz; let X' (i:P⊕N): Prop := i.isLeft
   have he' (i:Mound M):(heap M i).s.val.image o⊆ (heap M i).M.crest:=by cases i;exact X _; next i=> exact Menu.fills M _ i.2.val o X
   have hY1'(i:P⊕N): X' i→ Reader R d κ p l (M i).M:=by
       cases i; next h=> exact fun _=>hY1 h
       next=> intro h; exact False.elim (Bool.noConfusion h)
   choose! f hf using hY1'
   refine ⟨_,inferInstance,heap M, XPre.expoH M f,ψ,XPre.alphaH M X',he',fun j hj=>XPre.pres M X' f (fun i hi=> XPre.powered (hf i hi) he) hK h' hκ hp j hj, ?_, ?_, XPre.coast B M E F v w hw (fun _ _=>0) (fun _ _=>0) R' hpQ ?_ ?_ hD,?_⟩ -- args
   · refine ⟨fun i k=> (hψ i).shaped _,fun i k=> (hψ i).marked _,fun i=>?_⟩
     obtain ⟨c,hC,hE⟩:= (hψ i).toll; refine ⟨c,hE,le_trans ?_ (hγ i)⟩
     apply le_trans _ (mul_le_mul_of_nonneg_left (Extra.Multi.Budget.cap hC Finset.univ) (hw i).le); rw [Finset.mul_sum]; refine Finset.sum_le_sum fun j _=>?_ ; unfold reservedMass; rw [mul_left_comm]; apply mul_le_mul_of_nonneg_left _ (hw i).le; apply mul_le_mul_of_nonneg_right _ (hE j).1; rw [show C.p.supportExponent+1+1=C.p.supportExponent+2 by ring]
   · intro i j U; rw [freeze,show (∑ l,_) = _ from hO i j U, sub_add_cancel]
   · intro i; rw [Finset.sum_const_zero,add_zero]; exact hl i
   · intro i U; rw [add_zero]; exact hk i U
   apply XPre.fas M X' _ w hw hx; unfold banks; rw [Fintype.sum_sum_type]
   simp only [X',Sum.isLeft_inl, Sum.isLeft_inr, ↓reduceIte, Bool.false_eq_true,one_mul]
   rw [← Finset.mul_sum]; exact le_trans (add_le_add hv (mul_le_mul_of_nonneg_left hW (zero_le_one.trans hx))) hp0
end YM.LocalLTE.XPre
