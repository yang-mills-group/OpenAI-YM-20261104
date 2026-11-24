import YM.MergeProof.Accent
import YM.Integration.WilsonOriginalSignedHardHearing

/-! Vary one actual exponential and hard singleton in a shared original
`Served` representation. Its entire incoming mixed regular and forced family
remains in the signed response on every configuration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNamedSlotChange
open Finset Marker Lattice Wilson RG MergeProof MergeProof.Accent WilsonForcedMarkerLine
open WilsonOriginalSignedHardHearing
open scoped Classical BigOperators
variable {V : Type} [Fintype V] [DecidableEq V] {J : Census V}

def tilt {X : Type*} (actual:V→X→ℂ) (v:V) (d:X→ℂ) (z:ℂ) (i:V) (U:X) : ℂ :=
  if i=v then actual i U+z*d U else actual i U

omit [Fintype V] in
private theorem send (v:V) (a d z:ℂ) :
    Line v z (Poly.send (J.fire v) a) (Poly.send (J.fire v) (a+z*d))
      (Poly.send (J.fire v) (a+1*d)) := by
  constructor
  · intro m missing
    have ne:m≠J.fire v:=by
      intro eq
      apply missing
      rw [eq]
      exact mem_singleton_self v
    simp [sub_eq_add_neg,Poly.part_plus,Poly.part_neg,Poly.part_send,ne]
  · ext1 m
    simp only [Poly.part_send,Poly.part_plus,Poly.part_smul,sub_eq_add_neg,Poly.part_neg]
    split <;> ring

private theorem mass {X:Type*} (f:V→X→ℂ) (v:V) (d:X→ℂ) (z:ℂ) (U:X) :
    Line v z (Mach J (fun i=>f i U))
      (Mach J (fun i=>tilt f v d z i U)) (Mach J (fun i=>tilt f v d 1 i U)) := by
  apply finite univ
  intro i _
  by_cases eq:i=v
  · simpa only [eq,tilt,if_true,ite_true] using send (J:=J) v (f v U) (d U) z
  · simpa only [tilt,if_neg eq] using same (v:=v) (q:=z) (Poly.send (J.fire i) (f i U))

private theorem passed {a b c:Poly J} {v:V} {z:ℂ} (h:Line v z a b c) :
    Line v z (Poly.pass a) (Poly.pass b) (Poly.pass c) := by
  unfold Poly.pass
  exact finite _ _ _ _ (fun i _=>scaled (power h i) _)

variable {G:Gauge} {n:Side}
variable (P:Rep G n) (F:V → Config G n→ℂ) (ω:V→Box n → Config G n→ℂ)
  {X:Config G n→Poly J} {o:V→Site n} {w:V→ℝ} {a b:ℝ}

theorem original (funded:Served P F ω X o w a b) (v:V)
    (d:Config G n→ℂ) (k:Box n → Config G n→ℂ) :
    ∃ Y:ℂ → Config G n→Poly J, Y 0=X ∧
      (∀z,Served P (tilt F v d z) (fun i s=>tilt (fun j=>ω j s) v (k s) z i) (Y z) o w a b) ∧
      ∀z U,Line v z (X U) (Y z U) (Y 1 U) := by
  obtain ⟨H,K,cart,head,hard,rfl⟩:=funded
  let Y z:=restore P (tilt F v d z) (fun i s=>tilt (fun j=>ω j s) v (k s) z i) H K
  have zero:Y 0=restore P F ω H K:=by
    have hF:tilt F v d 0=F:=by funext i U; simp [tilt]
    have hω:(fun i s=>tilt (fun j=>ω j s) v (k s) 0 i)=ω:=by funext i s U; simp [tilt]
    dsimp only [Y]
    rw [hF,hω]
  refine ⟨Y,zero,fun z=>⟨H,K,cart,head,hard,rfl⟩,?_⟩
  intro z U
  unfold Y restore
  apply scaled
  apply product
  · exact passed (plus (mass F v d z U) (same _))
  · unfold MergeProof.Accent.field
    apply finite univ
    intro B _
    unfold grid
    split_ifs
    · apply products
      intro t _
      exact plus (plus (same _) (mass (fun j=>ω j t) v (k t) z U)) (same _)
    · exact same _

end YM.Integration.WilsonOriginalNamedSlotChange
