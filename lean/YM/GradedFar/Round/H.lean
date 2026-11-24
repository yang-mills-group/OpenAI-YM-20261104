import YM.GradedFar.Round.Purchase
import YM.GradedFar.Physical.Away

/-!
# H form on the same appointments, using the Ledger
-/
namespace YM.FVA2.GradedFar.Physical.Round
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh
open Moving Growth Pose Books Scale Dframe Jury Facets
open Continuation Continuation.Window
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h k t p : ℕ} {I V:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "ν"=> Teller.logNu 1
local notation "α"=> Measure.adjust N.scheme N.criterion
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (J K : FramesH P)
    (X : (d:ℕ)→ℝ→FieldEnd G d) (Y : (d:ℕ)→ℝ→ Prediction G d) (θ : ℝ→ℝ)
    (W : Bookshelf N U J K X Y θ) (Q : Earned N M U J K θ)
    (hq : ∀ᶠ r in τ,∀ u : Sec G h,K r h u= J r h (X h r u))
local notation "F"=> familyPoint U J h
local notation "Fρ"=> familyPoint U K h
-- b any T; pay during transfer to the NEW parameters with same t.
variable (b:Board I)
lemma lends (s:Finset V){x:V→I→ℂ}{t:I→ℝ}{P:V→I→PowerSeries ℂ}(h:∀ j∈s,Priced b p t 0 (x j) (P j)) :
    Priced b p t 0 (fun i=>∑ j∈s,x j i) (fun i=>∑ j∈s,P j i) := by
   refine ⟨fun i hi=>?_,?_⟩
   · simp only [map_sum]; exact Bill.sum s fun j hj=> (h j hj).1 i hi
   simp_rw [crop_sum,← Finset.sum_sub_distrib]; exact Bill.sum s fun j hj=> (h j hj).2
variable (r:I→ℝ){Z:Set (Points n)}{S:Set (Points m)}
variable (P':I→XSet Z S) (hr : Tendsto r b.l τ) (hb:b.g=gYM G∘r)
local notation "T"=>b.l
local notation "z"=>fun i=>flute (P' i) (b.s i)
include H W Q hq hr hb
theorem just_payment (p:ℕ) (v:Tags G h (n+m)) (he:∀ a: Tags G h (n+m), Priced b p (θ∘r) 0 (fun i=> F (r i) (n+m) (z i) a) (fun i=> Pose.line N (z i) a)):
    Priced b p (θ∘r) 0 (fun i=> Fρ (r i) (n+m) (z i) v) (fun i=>boundary N v (z i)) := by
   have ht : ∀ᶠ i in T,|(θ∘r) i|≤ 2*b.g i:=by rw [hb]; exact (hr.eventually (paid_reading simple θ Q.clock)).mono fun i hi=> hi.2.2.2
   let R' := fcols (α h) v; let S i:= F (r i) (n+m) (z i); let s i := X h (r i); let t:= θ∘r; let V i:= ⇑(s i) ∘ v
   let Y' a i:= combo (V i) a; let Φ (a:Choices G (fun _:Fin (n+m)=>h)) i:= Pose.line N (z i) (basisInputs a)
   have hΓ (a:Choices G (fun _:Fin (n+m)=>h)): Priced b p t 0 (Y' a) (fun i=> factors a R') := by
      have h (j:Fin (n+m)): Priced b p t 0 (fun i=> coord (a j) (V i j)) (fun i=> mode (R' j) (a j)) := by
         obtain y:= priced_column T (p:=p) (primary T N M r hr H θ (W.layers h)) (a j) (v j)
         refine ⟨Ledger.const _,?_⟩; apply enroll; rw [hb]; simpa only [R',V,s,t,Function.comp_apply,fcols,crop_eq,mode,coeff_mk,blend,smul_eq_mul] using y.2
      simpa only [combo,Y',factors, Finset.sum_const_zero] using Priced.product (p:=p) (t:=t) ht Finset.univ (fun _=>0) (fun j _=> h j)
   let E := (Finset.univ:Finset (Choices G (fun _:Fin (n+m)=>h)))
   have hy: Priced b p t 0 (fun i=> ∑ j∈E,Y' j i * S i (basisInputs j)) (fun i=> ∑ j∈E,factors j R'* Φ j i):= lends b _ fun j _=> by simpa only [zero_add] using Priced.prod ht (hΓ j) (he (basisInputs j))
   rw [show (fun i=>boundary N v (z i)) = _ from (show _=(fun i=> ∑ j∈E,factors j R'* Φ j i) from (by
     unfold boundary Φ Pose.line; simp_rw [show ∀ x:Points (n+m), fxt (book N h) x=status (α h) (fxt (Pose.Bbook N h) x) from fun x=> Jury.fxt_m _ _ x, against]; rfl) )]
   refine ⟨hy.1, hy.2.apply_eq ?_⟩
   filter_upwards [hr.eventually hq] with i hi
   rw [show ∑ j∈E,Y' j i*S i (basisInputs j)= S i (V i) from (basis_spelling _ _).symm]; refine congrArg (·-_) ?_
   apply congrArg (P.classMoment _ (fun _:Fin (n+m)=>h) (r i • z i)); funext j; exact (hi (v j)).symm
end
end YM.FVA2.GradedFar.Physical.Round
