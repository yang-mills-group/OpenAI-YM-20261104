import YM.Integration.WilsonThermometerUnitFilingFourPoolPacket
import YM.Next.UV_STRESS.Vary

/-! The four signed Wilson readings of two representatives of the same public
field. Each corner uses the same lattice test, original probability and limit. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFourSquare
open Filter Set Extraction Spec Table
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {l : Filter (ℕ×ℕ)} [l.NeBot] {n : ℕ}

/-- A cutoff label with its limiting representative on this extraction. -/
structure Arm (C : Family G) (S : Table C.book) (l : Filter (ℕ×ℕ))
    (d : ℕ) (v : S.Field d) where
  source : ℕ×ℕ → C.label d
  label : C.label d
  approaches : Tendsto source l (𝓝 label)
  represents : S.project d label = v

def reflected (F : Final C f S) {d : ℕ} {v : S.Field d}
    (A : Arm C S l d v) (s : Signed) :
    Arm C S l d (S.mirror F.room.kernel.spin d s (S.conj F.room.kernel.spin d v)) where
  source z := C.book.mirrorGroup d s (star (A.source z))
  label := C.book.mirrorGroup d s (star A.label)
  approaches := (C.book.mirrorGroup d s).continuous_of_finiteDimensional.continuousAt.tendsto.comp A.approaches.star
  represents := congrArg (fun x => S.mirror F.room.kernel.spin d s
    (S.conj F.room.kernel.spin d x)) A.represents

variable {d : Caps n} {v : (i : Fin n) → S.Field (d i)}

/-- The actual finite torus sum before either cutoff limit. -/
def marked (rows : ∀ i, Bool → Arm C S l (d i) (v i)) (pick : Fin n → Bool)
    (t : Test n) (u : ℕ×ℕ) : ℂ :=
  Order.smears C u.1 u.2 (fun i => ⟨d i,(rows i (pick i)).source u⟩) t

theorem measured (F : Final C f S) (order : l ≤ f.fuse)
    (rows : ∀ i, Bool → Arm C S l (d i) (v i)) (pick : Fin n → Bool) (t : Test n) :
    Tendsto (marked rows pick t) l
      (𝓝 (t.applyTo (fun x => S.classMoment S d x v))) := by
  let y : C.book.Vector d := fun i => (rows i (pick i)).label
  have paid := Next.UVStress.calibrated_smear (d:=d) F.room.ordered l order t
    (v:=fun z i => (rows i (pick i)).source z) (x:=y) (fun i => (rows i (pick i)).approaches)
  have eq : S.integralOn d y t = t.applyTo (fun x => S.classMoment S d x v) := by
    apply t.apply_eq
    intro x hx
    have same := S.class_agrees S F.room.kernel.laws.toSymmetric (fun _ => le_rfl) d hx y
    have names : (fun i => S.project (d i) (y i)) = v := funext fun i => (rows i (pick i)).represents
    rw [names] at same
    exact same.symm
  exact eq ▸ paid

variable {D : Caps 2} {w : (i : Fin 2) → S.Field (D i)}

/-- Keep both mixed numerators, with their signs and original finite density. -/
def contrast (rows : ∀ i, Bool → Arm C S l (D i) (w i)) (t : Test 2) (u : ℕ×ℕ) : ℂ :=
  (marked rows ![false,false] t u - marked rows ![false,true] t u) -
    (marked rows ![true,false] t u - marked rows ![true,true] t u)

theorem original (F : Final C f S) (order : l ≤ f.fuse)
    (rows : ∀ i, Bool → Arm C S l (D i) (w i)) (t : Test 2) :
    Tendsto (contrast rows t) l (𝓝 0) := by
  have each (a b : Bool) := measured F order rows ![a,b] t
  unfold contrast
  have ht := ((each false false).sub (each false true)).sub ((each true false).sub (each true true))
  simp only [sub_self] at ht
  exact ht

theorem weighted {ι : Type*} (Q : Finset ι) (coef : ι → ℂ) (F : Final C f S)
    (order : l ≤ f.fuse) (rows : ι → ∀ i, Bool → Arm C S l (D i) (w i))
    (tests : ι → Test 2) :
    Tendsto (fun z => ∑ j ∈ Q, coef j * contrast (rows j) (tests j) z) l (𝓝 0) := by
  simpa only [mul_zero, Finset.sum_const_zero] using tendsto_finsetSum Q
    (fun j _ => (original F order (rows j) (tests j)).const_mul (coef j))

end YM.Integration.WilsonThermometerUnitFilingFourSquare
