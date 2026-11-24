import YM.Integration.WilsonOriginalSuspendedWord
import YM.Integration.WilsonOriginalGroupInkSupport
import YM.Integration.WilsonOriginalResidentAngles

/-! Thermal slots have one possible seat. Each angular slot must reside in the actual original word. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSuspendedFootprint
open Function Finset Lattice RG Wilson Marker Push Push.AbsoluteSums Animals QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Poetry Exterior Stationary
open WilsonOriginalGroupInkSupport WilsonOriginalLinkedAngularPage WilsonOriginalSuspendedWord
open WilsonEmittedRootedJetWage WilsonOriginalResidentAngles WilsonOriginalCenteredSeamSalary
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n:Side} {V X:Type} [DecidableEq V] {o:Passport n V} {J:Census V}

def trace {r:ℕ} (u:Fin r→Slot G n):Finset (Site n):=
  univ.biUnion fun i=>(u i).elim ∅ (fun y=>{y.1})

def «at» (T:Row o J G X) (t:X) (extra r:ℕ) (u:Fin r→Slot G n) : ℂ :=
  iteratedFDeriv ℝ r (colored T t extra) 0 (peg G n ∘ u)

theorem away (T:Row o J G X) (t:X) (extra r:ℕ) (u:Fin r→Slot G n) (i:Fin r) (y:Site n×Loc G 1)
    (held:u i=some y) (off:y.1∉T.atom.footprint T.center) : «at» T t extra r u=0 := by
  let Q:=keep G (T.atom.footprint T.center)
  let P:Split G n→L[ℝ]Split G n:=(ContinuousLinearMap.id ℝ ℝ).prodMap Q
  let R:=split G n
  let F:Split G n→ℂ:=fun z=>T.paint t*(raw T extra z:ℝ)
  have eq:F=F ∘ P:=by
    funext z
    change T.paint t*((z.1^_*Helmet.frame T.atom T.center z.2):ℝ)=
      T.paint t*((z.1^_*Helmet.frame T.atom T.center (Q z.2)):ℝ)
    rw [congrFun (field T.atom T.center) z.2];rfl
  have smooth:ContDiffAt ℝ r F 0:=
    contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 ((WilsonOriginalSuspendedWord.smooth T extra).of_le le_top))
  have zero:P (R ((peg G n ∘ u) i))=0:=by
    rw [Function.comp_apply,held]
    apply Prod.ext
    · rfl
    · change Q (edgeColor.symm (edgeColor (ray G y)))=0
      rw [ContinuousLinearEquiv.symm_apply_apply]
      funext q
      change (if q.1∈T.atom.footprint T.center then (if q=y then (1:ℝ) else 0) else 0)=0
      by_cases e:q=y
      · subst q;simp [off]
      · simp [e]
  unfold «at»
  rw [WilsonOriginalSuspendedWord.original,Next.Foundations.jets_linear R smooth,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change iteratedFDeriv ℝ r F 0 _=0
  conv_lhs => rw [eq]
  rw [Next.Foundations.jets_linear P smooth,ContinuousMultilinearMap.compContinuousLinearMap_apply]
  exact (iteratedFDeriv ℝ r F 0).map_coord_zero i zero

abbrev Chairs (T:Row o J G X) (r:ℕ):=Fin r→Option ((T.atom.footprint T.center)×Loc G 1)

def visit (T:Row o J G X) {r:ℕ} (a:Chairs T r) : Fin r→Slot G n :=fun i=>
  (a i).map fun q=>(q.1.val,q.2)

theorem authentic (T:Row o J G X) {r:ℕ} (a:Chairs T r):trace (visit T a)⊆T.atom.footprint T.center:=by
  intro x h
  obtain ⟨i,_,h⟩:=mem_biUnion.mp h
  cases e:a i with
  | none=>simp [visit,e] at h
  | some y=>simpa [visit,e] using (show x∈T.atom.footprint T.center by
      have eq:x=y.1.val:=by simpa [visit,e] using h
      exact eq.symm ▸ y.1.property)

theorem unique (T:Row o J G X) (r:ℕ):Injective (visit (r:=r) T):=by
  intro a b e
  funext i
  have h:=congrFun e i
  cases ha:a i <;> cases hb:b i <;> simp [visit,ha,hb] at h ⊢
  exact Prod.ext h.1 h.2

theorem volume (T:Row o J G X) (r:ℕ) (b:ℝ) (hb:0<b):
    (Fintype.card (Chairs T r):ℝ) ≤ fare b (Fintype.card (Loc G 1)+1) r*Real.exp (b*T.length):=by
  have inside:T.atom.footprint T.center ⊆ neighbors T.length T.center:=by
    intro u h;exact (neighbors_mem ..).mpr (T.binder.spread T.atom (T.binder.footprint T.atom h))
  have k:=(card_le_card inside).trans (neighbors_card T.length T.center)
  have one:1≤ballCost T.length:=by
    unfold ballCost
    exact Nat.one_le_pow _ _ (by omega)
  apply le_trans _ (polynomial b hb T.length (Fintype.card (Loc G 1)+1) r)
  apply Nat.cast_le.mpr
  rw [show Fintype.card (Chairs T r)=((T.atom.footprint T.center).card*Fintype.card (Loc G 1)+1)^r by simp [Chairs]]
  apply Nat.pow_le_pow_left
  rw [Nat.mul_add,Nat.mul_one]
  exact Nat.add_le_add (Nat.mul_le_mul_right _ k) one

end YM.Integration.WilsonOriginalSuspendedFootprint
