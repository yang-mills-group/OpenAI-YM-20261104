import YM.Integration.WilsonEmittedWindingBalance
import YM.Integration.WilsonEmittedFiledValues
import YM.Integration.WilsonOriginalFlatHull

/-! A native healthy-halo comparison of the signed filed compact catalogues, with every angular, length and unmasked group price taken from their actual incomes. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFiledNativeCrop
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
variable (tube : LinkTube G) {k m j l D a₀ J : ℕ} {y o : Site n} {W ε : ℝ}
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
theorem original {q₀:ℕ}(closed:∀a,q₀+ν a=ℓ a+(Launch.index Γ (grades a) s.val+1))
    (hε:0≤ε)(read:∀i<j,∑u:Fin i→WilsonEmittedRootedJetWage.Slot G n,
      ‖iteratedFDeriv ℝ i full 0 (WilsonEmittedRootedJetWage.peg G n ∘ u)‖≤ε)
    (same:∀a,(P a).origin v=o)(positive:0<g)(small:g≤1)(hj:j≤J)(hl:l≤j)
    (inside:2*m≤k)(apart:k<B.B)(room:Room B n tube B.B W):
    WilsonOriginalFlatHull.Crop B tube o (sum total g) 0 (sum far g) l J W
      ((j:ℝ)*ε+fee 0*g^(j-l)) (fee 0) (fee m) (g^q₀*hardCap):=by
  have whole:=funded M w grades x c ℓ B old scope s.val v hv J 0 total (fun _ _ h=>⟨h,Nat.zero_le _⟩)
  have short:=funded M w grades x c ℓ B old scope s.val v hv J 0 near (fun _ _ h=>⟨h.1,Nat.zero_le _⟩)
  have unit:‖((g,0):Chart G n)‖≤1:=by simp [Prod.norm_def,abs_of_pos positive,small]
  have base:=whole (g,0) unit
  have long:=funded M w grades x c ℓ B old scope s.val v hv J m far (fun _ _ h=>h) (g,0) unit
  have partition:sum total g - 0 - sum far g=sum near g:=by
    funext U
    have split:sum total g U=sum near g U+sum far g U:=by
      simp only [words,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [divided (M a) (q a) (grades a) (paid a) s.val m g U]
      simp only [smul_add]
    change sum total g U-0-sum far g U=sum near g U
    rw [split];abel
  have support (a:A):=WilsonEmittedWordFootprint.kept (M a) s.val m v hv (q a) B g inside
  have physical (a:A):=local_field (M a) (q a) (grades a) (paid a) s.val B m v hv g
  refine ⟨⟨k,apart,?_⟩,?_,room,hl.trans hj,?_,?_,?_,WilsonEmittedCouplingSlice.fixed long,?_,?_⟩
  · rw [partition]
    intro U U' agrees
    apply Finset.sum_congr rfl
    intro a _
    rw [support a U U' (by simpa only [same a] using agrees)]
  · rw [partition]
    intro t U
    apply Finset.sum_congr rfl
    intro a _
    rw [(physical a).2.1 t U]
  · intro u hu
    rw [partition]
    exact WilsonEmittedCouplingSlice.fixed (short (g,u)
      (by change max ‖g‖ ‖u‖≤1;exact max_le (by simpa [abs_of_pos positive] using small) (hu.trans room.small)))
  · simpa only [sub_zero, Function.comp_def] using (WilsonEmittedCouplingSlice.fixed base).smooth
  · intro i hi
    simp only [sub_zero]
    apply WilsonEmittedWindingSlice.original full hj hl positive.le small base.nonneg hε
      (fun z hz=>whole z (hz.trans small)) _ i hi
    intro r hr
    exact WilsonEmittedRootedJetWage.original (iteratedFDeriv ℝ r full 0) (read r hr)
  · intro U
    have quote:=(WilsonEmittedFiledValues.quote M w grades x c ν B old scope s.val v hv far m
      (fun _ _ h=>h) U).2
    rw [WilsonEmittedFiledValues.recorded M w grades x c ν ℓ B old scope s.val v hv far m
      (fun _ _ h=>h) closed positive U,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (pow_pos positive q₀))] at quote
    exact (inv_mul_le_iff₀ (pow_pos positive q₀)).mp quote
  · exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hε) (mul_nonneg base.nonneg (pow_nonneg positive.le _))

end YM.Integration.WilsonOriginalFiledNativeCrop
end
