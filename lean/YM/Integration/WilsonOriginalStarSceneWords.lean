import YM.Integration.WilsonOriginalStarLaurentWallet
import YM.Integration.WilsonOriginalProjectedCurvatureArmada

/-! The marked scalar and every curvature monomial of an original fitted section,
as independently addressed invariant words on the reporting mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalStarSceneWords
open Function Finset Lattice Wilson RG Source Labels Marker LocalComparison QuadraticLocal
open Earn Sunrise PhysicalNext.Repeat.Legato ActualRunCurvaturePackets NativeCurvatureTensor
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {V : Type} (d : V → ℕ)
abbrev Entry := V ⊕ ((j : V) × WilsonOriginalStarLaurentWallet.Socket R (d j))

def root (i : Entry R d) : V := i.elim id Sigma.fst
def rank (i : Entry R d) : ℕ := i.elim (fun _=>0) (fun s=>s.2.2.val.sum (fun _ a=>a))
def pole (i : Entry R d) : ℕ := i.elim (fun _=>0) (fun s=>WilsonOriginalStarLaurentWallet.lag R (d s.1) s.2)

theorem low (i : Entry R d) : pole R d i ≤ rank R d i := by
  rcases i with j|⟨j,w,a⟩
  · exact le_rfl
  · exact (ofRun R (d j)).data.low w a.val a.property

def raw : (i : Entry R d) → Atom G (rank R d i)
  | .inl _ => ⟨Fin.elim0,fun _=>1⟩
  | .inr ⟨j,w,a⟩ => WilsonOriginalProjectedCurvatureAtom.atom
      (fun k=>(word a.val k).2) (fun k=>(ofRun R (d j)).data.columns w (word a.val k).1)

theorem lawful (i : Entry R d) : (raw R d i).Invariant := by
  rcases i with j|⟨j,w,a⟩
  · intro u x
    rfl
  · exact WilsonOriginalProjectedCurvatureAtom.invariant _ _

def constant : Entry R d → Prop
  | .inl _ => True
  | .inr _ => False

theorem clear (i : Entry R d) (h : constant R d i) : rank R d i=0 := by
  rcases i with j|s
  · rfl
  · exact False.elim h

def scalar (g τ : ℝ) (v : (j:V) → R.family.label (d j)) : Entry R d → ℂ
  | .inl j => v j 0
  | .inr ⟨j,s⟩ => WilsonOriginalStarLaurentWallet.coefficient R (d j) g τ
      ((R.family.labels.level (d j)).core (v j)) s

def normalizer {k : ℕ} (a : Atom G k) (σ : ℝ) := 1 + a.budget σ

theorem positive {k : ℕ} (a : Atom G k) (σ : ℝ) : 0 < normalizer a σ :=
  add_pos_of_pos_of_nonneg zero_lt_one (WilsonOriginalProjectedCurvatureSalary.amount a σ)

def unitAtom {k : ℕ} (a : Atom G k) (σ : ℝ) : Atom G k where
  leg := a.leg
  coeff j := (normalizer a σ)⁻¹ * a.coeff j

theorem evaluated {k : ℕ} (a : Atom G k) (σ : ℝ) (x : Fin k → G.Color) :
    (unitAtom a σ).poly x = (normalizer a σ)⁻¹ * a.poly x := by
  simp only [unitAtom,Atom.poly,Finset.mul_sum,mul_assoc]

theorem invariant {k : ℕ} (a : Atom G k) (σ : ℝ) (law : a.Invariant) :
    (unitAtom a σ).Invariant := fun u x=>by rw [evaluated,evaluated,law u x]

theorem unitPrice {k : ℕ} (a : Atom G k) (σ : ℝ) : (unitAtom a σ).budget σ ≤ 1 := by
  change (∑ j, |(normalizer a σ)⁻¹*a.coeff j|)*Real.exp (σ*a.length) ≤ 1
  simp only [abs_mul,abs_of_nonneg (inv_nonneg.mpr (positive a σ).le),←Finset.mul_sum]
  change (normalizer a σ)⁻¹ * a.magnitude * Real.exp (σ*a.length) ≤ 1
  rw [mul_assoc,inv_mul_le_iff₀ (positive a σ),mul_one]
  exact le_add_of_nonneg_left zero_le_one

variable [Fintype V]
def maximum := univ.sup (rank R d)
def tariff := maximum R d + 1

def loan (i : Entry R d) : Loan where
  e := rank R d i - pole R d i
  r := rank R d i
  toll := tariff R d
  higher := Nat.succ_pos _
  crest := by
    have h: rank R d i ≤ maximum R d:=le_sup (f:=rank R d) (mem_univ i)
    change _ ≤ _ + (maximum R d + 1) + 1
    omega

theorem lag (i : Entry R d) : (loan R d i).lag = -(pole R d i:ℤ) := by
  change ((rank R d i-pole R d i:ℕ):ℤ)-(rank R d i:ℤ)=_
  have h:=low R d i
  omega

end YM.Integration.WilsonOriginalStarSceneWords
