import YM.GradedFar.Physical.ScaleMeter

/-!
# Test the actual with the prescribed MS read and the actual calibrated θ
-/
namespace YM.FVA2.GradedFar.Physical.Address
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open OPE Orbits Logged Physical.Round
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h k j t p : ℕ} {I V:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "ν"=> Teller.logNu 1
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (K : FramesH P)
    (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin) (θ:ℝ→ℝ)
variable {X:Set (Points n)}{Y:Set (Points m)}
    {B C L L':ℝ}
local notation "Q₀"=>upper G C B

lemma exactly_alone (d:Fin n→ℕ) (r:ℝ)(x:Points n)(o:View U)(u: Inputs G d)(hx:r • x∈conf n) :
     Orbits.moment (spectator U o.1) (atPos r o.2 x) (here K r u)=alone U K o r x u := by
    unfold alone whole; rw [observed,observed]
    let e:Fin n⊕ Fin 0≃ Fin n:={ toFun:= Sum.elim id Fin.elim0, invFun:=Sum.inl,left_inv:=fun j=>by cases j with| inl i=>rfl| inr i=>exact i.elim0, right_inv := fun _=>rfl }
    rw [← perm_observe (spectator U o.1) (spectate U o.1).laws.toSymmetric e (Orbits.names (here K r u)) (show Injective (atPos r o.2 x) from fun i j h=> hx (show (r • x) i=(r • x) j from add_left_cancel h))]
    congr 1 <;> funext t <;> cases t with
       | inl a => rfl
       | inr a => exact a.elim0
include H
lemma pricing (x:Points n)(v: Tags G h n)(hc:x∈conf n) : Wave.value N M x v=
     Moving.shop ((Wave.transformed N M h) n ⟨x,hc⟩) v:=by
     rw [Wave.value,Wave.on_book N M H]; rw [← Round.teller_spells N M H]; unfold Physical.boundary; rw [Scale.Jury.fxt,dif_pos hc]
-- keep actual determinant for each viewer

def sees (d:ℕ)(w:Continuation.Window)(i:View U): Matrix (Toon G d) (Toon G d) ℂ :=
    fun b a=> Dwide U K w i RootG (Continuation.Margin.probe b) (theory a)
omit H in
lemma visibly (w:Continuation.Window)(i:View U): sees U K h w i=Continuation.Margin.measuredAt (adjusted K) (Y0 U K (fun _ : Fin 1 => h) (fun _:Fin 1=>h)) w i := by
    ext a b; exact center_same ..
variable (he : Tendsto (fun i=> θ i/gYM G i) τ (𝓝 1)) (ht:Towards N M U K θ Q)

include ht he
open Continuation.Stretch Continuation.Margin
lemma sees_enough (k d:ℕ)(η c:ℝ)(hC: c ≤ C) (hc:0<c) (hp: Deep p k B d d η)(hB:0<B)(hη:0<η): ∃ D:ℝ,0<D ∧
     ∀ᶠ (w:Continuation.Window) in windows (band G c C B),∀ i,
       IsUnit (sees U K d w i)∧∀ a b, ‖(sees U K d w i)⁻¹ a b‖≤ D*w.Stretch^d := by
    simp_rw [visibly]; apply pivot_safe H θ hB hc hC he hp hη
    let X:Set (Points 1):={0}; let S:Set (Points 1):={RootG}
    have hX:X⊆conf 1:=singleton_subset_iff.mpr fun _ _ _=>Subsingleton.elim ..
    exact ht.first_line 1 1 _ _ X S B C hB (hc.trans_le hC) isCompact_singleton hX isCompact_singleton (singleton_subset_iff.mpr ok_wall) p

set_option linter.unusedSectionVars false in
lemma complete_correlation (hX:IsCompact X)(hx:X⊆conf n)(d:Fin n→ℕ)(p:ℕ)(L:ℝ): ∃ D:ℝ,0<D ∧ ∀ᶠ r in τ,∀ i:View U,∀x∈X,∀u:Inputs G d, Within L u →
      ‖Orbits.moment (spectator U i.1) (atPos r i.2 x) (here K r u) - crop p (θ r) (Wave.value N M x u)‖ ≤ D*θ r^(p+1) := by
   obtain ⟨D,hD,H⟩:= ht.kernel n d X hX hx p L; refine ⟨D,hD,?_⟩; filter_upwards [self_mem_nhdsWithin,H] with r (hr:0<r) h i x he u hu; rw [exactly_alone U K d r x i u (Round.present hr (hx he))]; exact h i x he u hu
end
end YM.FVA2.GradedFar.Physical.Address
