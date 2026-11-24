import YM.Integration.WilsonThermometerRegisteredCenteredHeldPurchase
import YM.Work.F03.Transport

/-! Actual transported-curvature words for the captured ordinary product. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCapturedWords
open YM.Lattice YM.RG YM.Wilson Finset
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {k l:ℕ}

def rooted (w:Walk) (a:Slot) : Slot := ⟨w++a.walk,a.plaq⟩

private lemma face (w:Walk) (a:Slot) (y:Site n) :
    Work.F03.slotFace (rooted w a) y = Work.F03.slotFace a (stop y w) := by
  have endAt (x:Site n) (z:Walk) : wrap n (stop (0:Cover) z)+x=stop x z := by
    have shift (v:Walk) (b:Site n): stop b v+x=stop (b+x) v := by
      induction v generalizing b with
      | nil=>rfl
      | cons d t ih=>rw [stop,stop,ih,add_right_comm b]
    rw [wrap_stop_cover,map_zero,shift,zero_add]
  apply Prod.ext
  · change wrap n (stop (0:Cover) (w++a.walk)) + y = wrap n (stop (0:Cover) a.walk) + stop y w
    rw [endAt,stop_append,endAt]
  · rfl

theorem slot (w:Walk) (a:Slot) (U:Config G n) (y:Site n) :
    (rooted w a).atSite U y=G.adjoint (travel U y w) (a.atSite U (stop y w)) := by
  rw [Work.F03.atSite_path,Work.F03.atSite_path,face,←G.adjoint_mul]
  change G.adjoint (travel U y (w++a.walk)) _=_
  rw [travel_append]

def move (w:Walk) (A:Atom G k) : Atom G k := ⟨fun i=>rooted w (A.leg i),A.coeff⟩

@[simp] theorem moved (w:Walk) (A:Atom G k) (law:A.Invariant) (U:Config G n) (y:Site n) :
    (move w A).unmasked U y=A.unmasked U (stop y w) := by
  unfold Atom.unmasked
  change A.poly (fun i=>(rooted w (A.leg i)).atSite U y)=_
  simp_rw [slot]
  apply law

@[simp] theorem reach (w:Walk) (A:Atom G k) :
    (move w A).length = k*w.length + A.length := by
  unfold Atom.length
  simp only [move,rooted,Slot.length,List.length_append,add_assoc,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rfl

def joined (A:Atom G k) (B:Atom G l) : Atom G (k+l) where
  leg := Fin.append A.leg B.leg
  coeff c := A.coeff (fun j=>c (Fin.castAdd l j)) * B.coeff (fun j=>c (Fin.natAdd k j))

private lemma expansion (f:(Fin k→G.ColorIndex)→ℝ) (h:(Fin l→G.ColorIndex)→ℝ) :
    (∑ c : Fin (k+l)→G.ColorIndex, f (fun j=>c (Fin.castAdd l j))*h (fun j=>c (Fin.natAdd k j))) =
      (∑ a,f a)*(∑ b,h b) := by
  rw [←(Fin.appendEquiv k l).sum_comp, Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  change f (fun j=>(Fin.append a b) (Fin.castAdd l j))*h (fun j=>(Fin.append a b) (Fin.natAdd k j))=_
  simp

theorem polynomial (A:Atom G k) (B:Atom G l) (x:Fin (k+l)→G.Color) :
    (joined A B).poly x = A.poly (fun j=>x (Fin.castAdd l j))*B.poly (fun j=>x (Fin.natAdd k j)) := by
  unfold Atom.poly
  rw [←expansion]
  apply Finset.sum_congr rfl
  intro c _
  rw [Fin.prod_univ_add]
  change _*_ * (_*_) = _*_ * (_*_)
  ring

theorem closed (A:Atom G k) (B:Atom G l) (a:A.Invariant) (b:B.Invariant) : (joined A B).Invariant := by
  intro t x
  rw [polynomial,polynomial,←a t (fun j=>x (Fin.castAdd l j)),←b t (fun j=>x (Fin.natAdd k j))]

theorem group (A:Atom G k) (B:Atom G l) (U:Config G n) (y:Site n) :
    (joined A B).unmasked U y=A.unmasked U y*B.unmasked U y := by
  unfold Atom.unmasked
  rw [polynomial]
  simp [joined]

theorem length (A:Atom G k) (B:Atom G l) :
    (joined A B).length = A.length + B.length := by
  unfold Atom.length
  rw [Fin.sum_univ_add]
  simp [joined]

theorem size (A:Atom G k) (B:Atom G l) :
    (joined A B).magnitude = A.magnitude * B.magnitude := by
  unfold Atom.magnitude
  simp only [joined,abs_mul]
  exact expansion (G:=G) (fun x=>|A.coeff x|) (fun x=>|B.coeff x|)

theorem original (A:Atom G k) (B:Atom G l) (a:A.Invariant) (b:B.Invariant)
    (w v:Walk) (U:Config G n) (y:Site n) (σ:ℝ) :
    let T:=joined (move w A) (move v B)
    T.Invariant ∧ T.unmasked U y=A.unmasked U (stop y w)*B.unmasked U (stop y v) ∧
      T.budget σ=A.budget σ*B.budget σ*Real.exp (σ*((k*w.length+l*v.length:ℕ):ℝ)) := by
  dsimp only
  refine ⟨closed _ _ a b,?_,?_⟩
  · rw [group,moved _ _ a,moved _ _ b]
  · unfold Atom.budget
    rw [size,length,reach,reach]
    change A.magnitude*B.magnitude*Real.exp _=_
    rw [show σ*(((k*w.length+A.length+(l*v.length+B.length):ℕ):ℝ))=
      σ*(A.length:ℝ)+σ*(B.length:ℝ)+σ*((k*w.length+l*v.length:ℕ):ℝ) by push_cast;ring,
      Real.exp_add,Real.exp_add]
    ring

end YM.Integration.WilsonThermometerRegisteredCapturedWords
