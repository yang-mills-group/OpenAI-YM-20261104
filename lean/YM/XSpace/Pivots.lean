import YM.FiniteVolumeClosure.A0bCompat.FDSpin
import YM.XSpace.WickJet
import YM.FiniteVolumeClosure.A0bCompat.FDSector
/-!
# Regulator point fields (before finite normalization)

Use the real orthogonal on-shell section on *linear* curl jets. This
choice uses the established harmonic projection of `Extra.FD`, common
with the MERGE comparator. All PT calculations themselves use only these
pivots from the independent Wilson flat-saddle rule. Coordinates not
constrained to any cooperative frame of MERGE.

Covariant basis-free convention throughout: input the actual homogeneous
on-shell real labels and extend ℂ-linearly. E.g. one may contract on any real
orthogonal basis simultaneously measuring the same fields.

Only address zero needed here: Wick-jet at top contact is a field-only
operation (extends trivially in test indices). Own horizon convention.
Engineering weight scaled by mesh in reference units, include unit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Set Filter Lattice Wilson Source Source.Drops MeasureTheory
open Next.Rank Normal Spindle Beamer Next.Foundations Configuration MvPolynomial LiftMark
open Extra.FD Maxwell
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators ContDiff Classical
variable (G : Gauge) (d : ℕ)

abbrev SPACE := ↥(shellSector G d)
def readSpace : Labels.Label G d →ₗ[ℂ] SPACE G d := (observable G d).rangeRestrict

def sectionMap : SPACE G d →ₗ[ℂ] Labels.Label G d:= (writeRaw.toLinearMap.comp ((shellSector G d).subtype)).codRestrict _ (by
    intro p; obtain ⟨hp,hv⟩ := (past_sector _).1 p.property; constructor
    · exact filterMove costKey Labels.generation writeRaw (gradientWrite (·+2)) (show p.val∈byWeight costKey (Set.Iic d) from hp)
    intro J u
    change Labels.read _ (writeRaw p.val)=Labels.read _ (writeRaw p.val); rw [writeRaw_read,writeRaw_read,show reroute (Labels.colored u J)=stain u (reroute J) from funext fun i => send_color (j:=i) u (J i)]
    exact hv u _)
lemma contracts_down (p : SPACE G d): readSpace G d (sectionMap G d p)=p := Subtype.ext (writeRaw_after p.val)

variable {G d}
def rot (s: Ortho) (p:SPACE G d) := readSpace G d (Labels.tensor s (sectionMap G d p))
def starS (p:SPACE G d) := readSpace G d (Labels.realBar (sectionMap G d p))
lemma rotate_section (p:SPACE G d) (s: Ortho) : sectionMap G d (rot s p)=Labels.tensor s (sectionMap G d p):= by
  apply Subtype.ext; apply Labels.eval_ext; intro J
  change Labels.read J (writeRaw (reduceEq _)) = Labels.read _ (Labels.rotated _ _)
  change Labels.read J (writeRaw (reduceEq (Labels.rotated s (writeRaw p.val)))) = _
  simp only [Labels.rotated,writeRaw_read,jet_value,Labels.eval_changed]
  change probe _ p.val=Labels.read _ (writeRaw p.val)
  rw [writeRaw_read]; congr 2; funext i
  change sendTo G i (Labels.Taylor.turn s⁻¹ (gaugeJet (sendTo G i (J i))))=sendTo G i (Labels.Taylor.turn s⁻¹ (J i)); rw [send_spin, send_spin,sends_back]
lemma star_section (p:SPACE G d): sectionMap G d (starS p)=Labels.realBar (sectionMap G d p):= by
  apply Subtype.ext; apply Labels.eval_ext; intro J
  change Labels.read J (writeRaw (reduceEq (Labels.conjPol (writeRaw p.val))))=Labels.read _ (Labels.conjPol _)
  rw [writeRaw_read,jet_value,Labels.conj_value,Labels.conj_value, ← jet_value,writeRaw_after]
  rw [← writeRaw_read]; rfl

def Evident {M : Type*} [AddCommMonoid M] (w:ℕ → M) (p:SPACE G d) (m:M) := MvPolynomial.IsWeightedHomogeneous (fun i : Slot G => w i.1) p.val m
lemma pure_section {M : Type*} [AddCommMonoid M] (w:ℕ → M) (p:SPACE G d) (m:M) (h : Evident w p m):
    MvPolynomial.IsWeightedHomogeneous (fun i : Labels.Key G=> w i.1) (sectionMap G d p).val m:= gradeMove _ _ _ (gradientWrite w) _ _ h

def Weight (p:SPACE G d) := Evident (·+2) p d
abbrev own (G:Gauge) (d:ℕ) : Submodule ℂ (SPACE G d):=
  Submodule.comap ((shellSector G d).subtype) (MvPolynomial.weightedHomogeneousSubmodule ℂ costKey d)

lemma own_top (p: own G d): Weight p.val:= p.property

def vacuumS (G:Gauge): own G 0:=
  ⟨readSpace G 0 (Labels.unit G 0),by change IsWeightedHomogeneous costKey (reduceEq (G:=G) 1) 0; rw [map_one]; exact MvPolynomial.isWeightedHomogeneous_one ..⟩
@[simp] lemma vacuum_section (G:Gauge): sectionMap G 0 (vacuumS G).val=Labels.unit G 0 := Subtype.ext (show writeRaw (reduceEq 1)=_ by rw [map_one,map_one]; rfl)

def topV (p: own G d):= (W G d).symm ((Frame G d).coords (sectionMap G d p.val))
def stenc (p:own G d):= letters G d (topV p)
lemma weight_jet (P : own G d): Pi0 G d (milk (WickK G) (stenc P))=thawKey (sectionMap G d P.val):= pure_jet ..

namespace Regulator.Tree
variable {R:Regulator} (T:R.Tree)

def localWord (o:R.LSite) (p:(Frame G d).Coeff): T.SeriesC G := ∑ i:Index G d, PowerSeries.C (MvPolynomial.C (p i))*T.birth o i

def top (o:R.LSite) (p:own G d) := T.localWord o (topV p)

/-- Scale in the given mesh. -/
def scaledTop (o:R.LSite) (a : ℝ) (p:own G d):= PowerSeries.C (MvPolynomial.C ((↑(a^d) : ℂ)⁻¹))* T.top o p
lemma top0 (o:R.LSite) (p:own G d): PowerSeries.constantCoeff (T.top o p)=T.evaluateF G (rename (imprint o) (stenc p)) := by
  unfold top localWord stenc; rw [letters_unfold,map_sum,map_sum,map_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_mul,map_smul,map_smul,T.first o i (chosen i),PowerSeries.constantCoeff_C,C_mul']

@[simp] lemma top1 (o:R.LSite) (a:ℝ): T.scaledTop o a (vacuumS G)=1 := by
  let p := vacuumS G
  have he (A:T.Array G) : T.canonical o (0:Index G 0) A=1:=congr_fun (Next.Foundations.sound G 0).unit _
  have hd : T.birth o (0:Index G 0) = 1:= by
    have he': T.canonical o (0:Index G 0)=fun _=>1:= _root_.funext he
    simpa only [he',Formal.jet_C,map_one,Labels.Frame.zero_degree,pow_zero,mul_one] using T.birth_keeps o (0:Index G 0)
  unfold scaledTop top topV
  rw [vacuum_section,Labels.Frame.coords_unit,W_inv_u]; simp only [pow_zero,Complex.ofReal_one, inv_one,map_one,one_mul]
  unfold localWord Labels.Frame.e0; simp [Pi.single_apply,ite_mul,apply_ite MvPolynomial.C,apply_ite PowerSeries.C,hd]
end Regulator.Tree
end YM.XSpace
