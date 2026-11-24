import YM.Integration.WilsonEmittedWindingBalance
import YM.Integration.WilsonEmittedFiledValues
import YM.Integration.WilsonOriginalCommonWordTaylor

/-! One common compact field and the complete original angular and length prices for a finite roster of fronts. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFullRosterNativeCrop
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open QuadraticLocal.Sunrise
open AllOrder AllOrder.Floe Laurent Comparison.RG02 Comparison.Density Comparison.Density.Mirrors
open Transport AnalyticBridge.SectorAffine.Offset
open WilsonEmittedWordJointFare WilsonEmittedCutGrouping WilsonEmittedFiledCatalogue
open scoped BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {A V : Type} [Fintype A] [DecidableEq V]
variable {I X : A→Type} {Γ : Census V} {P : A→Passport n V}
variable (M : (a:A)→I a→Row (P a) Γ G (X a)) (w : A→V→ℝ) (grades : A→V→ℕ)
variable (x : (a:A)→X a) (c : A→ℝ) (ν ℓ : A→ℕ)
variable (B : BudgetPoint) {σ b K θ : A→ℝ} {p pieces depth : A→ℕ} {g : ℝ}
variable (old : ∀a,Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (pieces a) (depth a))
variable (scope : ∀a,Invoice.Supports B (K a) (B.supportExponent+2) g (σ a) (θ a))
variable (s : Multi.Hot Γ) (v : V) (hv : v∈s.val.val)
variable (tube : LinkTube G) {m j l J : ℕ} {W ε : ℝ}
local notation "q" a:max => (fun i:I a=>(M a i).paint (x a))
local notation "sum" => words M x c ℓ
local notation "near" => (fun a=>early (M a) s.val m)
local notation "far" => (fun a=>late (M a) s.val m)
local notation "total" => (fun a=>picked (M a) s.val)
local notation "full" => (fun z:Chart G n=>sum total z.1 (increment 1 z.2))
local notation "fee" u:max => rent (G:=G) w c ℓ B (p:=p) (pieces:=pieces) (depth:=depth)
  (b:=b) (α:=fun _=>B.supportExponent+2) (θ:=θ) s.val J u
local notation "paid" a:max => staff M w grades x B old scope a

local notation "hardCap" => WilsonEmittedLongInvoice.gross w c ν B s.val m g p pieces depth b θ


include scope old hv in
theorem original {H:Type} [Fintype H] (site:H→Site n)(owner:A→H)
    (fronts:∀a,(P a).origin v=site (owner a))
    {q₀:ℕ}(closed:∀a,q₀+ν a=ℓ a+(Launch.index Γ (grades a) s.val+1))
    (hε:0 ≤ ε)(read:∀i<j,∑u:Fin i→WilsonEmittedRootedJetWage.Slot G n,
      ‖iteratedFDeriv ℝ i full 0 (WilsonEmittedRootedJetWage.peg G n ∘ u)‖ ≤ ε)
    (positive:0<g)(small:g ≤ 1)(hj:j ≤ J)(hl:l ≤ j)
    (cutoff:m=WilsonOriginalSeparatedFrontClusters.crop B.B (Fintype.card H))
    (enrolled:64*(Fintype.card H+1) ≤ B.B)(room:Room B n tube B.B W)
    (U:Config G n)(bright:∀u,Healthy B.threshold (neighborhood B.B (site u)) U):
    ‖sum total g U‖ ≤ (l:ℝ)*(((j:ℝ)*ε+fee 0*g^(j-l))+fee m)+(fee 0)*W^l+g^q₀*hardCap:=by
  let k:=2*m+2
  have all:WilsonOriginalClusteredAxialDirection.Common site k tube W U:=by
    rw [show k=2*WilsonOriginalSeparatedFrontClusters.crop B.B (Fintype.card H)+2 by
      simp only [k,cutoff]]
    exact WilsonOriginalClusteredAxialDirection.cropped site B tube U enrolled room bright
  obtain ⟨_,X₀,dose,_,_,heard⟩:=all
  have whole:=funded M w grades x c ℓ B old scope s.val v hv J 0 total (fun _ _ h=>⟨h,Nat.zero_le _⟩)
  have short:=funded M w grades x c ℓ B old scope s.val v hv J 0 near (fun _ _ h=>⟨h.1,Nat.zero_le _⟩)
  have unit:‖((g,0):Chart G n)‖ ≤ 1:=by simp [Prod.norm_def,abs_of_pos positive,small]
  have base:=whole (g,0) unit
  have long:=funded M w grades x c ℓ B old scope s.val v hv J m far (fun _ _ h=>h) (g,0) unit
  have partition:sum total g=sum near g + sum far g:=by
    funext T
    change sum total g T=sum near g T+sum far g T
    simp only [words,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [divided (M a) (q a) (grades a) (paid a) s.val m g T]
    simp only [smul_add]
  have shared:sum near g (increment 1 X₀)=sum near g U:=by
    apply Finset.sum_congr rfl
    intro a _
    have loc:=WilsonEmittedWordFootprint.kept (M a) s.val m v hv (q a) B g
      (show 2*m ≤ k by dsimp only [k];omega)
    rw [fronts a] at loc
    have inv:=(local_field (M a) (q a) (grades a) (paid a) s.val B m v hv g).2.1
    rw [heard (owner a) _ loc inv]
  apply WilsonOriginalCommonWordTaylor.original (sum total g) (sum near g) (sum far g) U X₀
    (hl.trans hj) (B.threshold_pos.trans_le room.budget) room.small dose
    (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hε) (mul_nonneg base.nonneg (pow_nonneg positive.le _)))
    partition shared
  · intro X₁ bound
    exact WilsonEmittedCouplingSlice.fixed (short (g,X₁) (by
      change max ‖g‖ ‖X₁‖ ≤ 1
      exact max_le (by simpa [abs_of_pos positive] using small) (bound.trans room.small)))
  · simpa only [Function.comp_def] using (WilsonEmittedCouplingSlice.fixed base).smooth
  · intro i hi
    apply WilsonEmittedWindingSlice.original full hj hl positive.le small base.nonneg hε
      (fun z hz=>whole z (hz.trans small)) _ i hi
    intro r hr
    exact WilsonEmittedRootedJetWage.original (iteratedFDeriv ℝ r full 0) (read r hr)
  · exact WilsonEmittedCouplingSlice.fixed long
  · have quote:=(WilsonEmittedFiledValues.quote M w grades x c ν B old scope s.val v hv far m
      (fun _ _ h=>h) U).2
    rw [WilsonEmittedFiledValues.recorded M w grades x c ν ℓ B old scope s.val v hv far m
      (fun _ _ h=>h) closed positive U,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (pow_pos positive q₀))] at quote
    exact (inv_mul_le_iff₀ (pow_pos positive q₀)).mp quote

end YM.Integration.WilsonOriginalFullRosterNativeCrop
end
