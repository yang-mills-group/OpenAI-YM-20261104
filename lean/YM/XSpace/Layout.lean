import YM.XSpace.Geometry
import YM.Euclid.Test
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Large-period orbit regulator. Positions in the physical units of the chosen measurement length,
with a finite center protocol. At a fixed odd block ratio (can always use
a power of three) with an allowed fixed final side after returning to the IR. Keeping the
choice of large constants available is useful for later regulator bounds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Filter Set MeasureTheory Lattice
open scoped Topology ContDiff BigOperators

structure Mesh where
  p : Period
  spacing : ℝ
  positive : 0<spacing

/-- family of allowed regulator sequences (parameterized for fixed-order costs) -/
structure Run where
  ratio : ℕ
  odd : Odd ratio
  reserve : ℕ
  finalSide : Period
  large : 3≤ratio
  spare : 1≤reserve
namespace Run
variable (V : Run)
def den (n : ℕ) := V.ratio ^ n
theorem den_pos (n : ℕ) : 0< V.den n := pow_pos (by have h:=V.large; omega) n

def side (n : ℕ):= V.finalSide.side.val*V.den (n+V.reserve*n*n)
def period (n : ℕ) : Period :=
    ⟨⟨V.side n, Nat.mul_pos V.finalSide.side.pos (V.den_pos _)⟩,
      dvd_mul_of_dvd_left V.finalSide.even _, V.finalSide.large.trans (Nat.le_mul_of_pos_right _ (V.den_pos _))⟩

def step (n : ℕ) : Mesh:=⟨V.period n,(V.den n:ℝ)⁻¹, inv_pos.mpr (by exact_mod_cast V.den_pos n)⟩
end Run
namespace Mesh
variable (p : Mesh)
abbrev Sites := p.p.Sites
def size := p.spacing * p.p.side.val
lemma size_pos : 0<p.size := mul_pos p.positive (by exact_mod_cast p.p.side.pos)
theorem run_size (V : Run) (n : ℕ) : (V.step n).size=(V.finalSide.side.val:ℝ)*V.ratio^(V.reserve*n*n):=by
  have hp:(V.ratio:ℝ) ≠ 0:= by have he:=V.large; exact_mod_cast (show V.ratio≠0 by omega)
  change (↑(V.ratio ^ n):ℝ)⁻¹ * ↑(V.finalSide.side.val*V.ratio^(n+V.reserve*n*n))= _; push_cast; rw [pow_add]; field_simp

def Box := Icc (fun _ : Axis=>p.size/8) (fun _=>p.size/4)
theorem compact_box : IsCompact p.Box := isCompact_Icc

def vol := volume.real p.Box
theorem vol_pos : 0<p.vol:=by
  let A : Set (Four ℝ):= Set.pi (univ : Set Axis) fun _=>Ioo (p.size/8) (p.size/4)
  have h : Set.Nonempty A :=⟨fun _=>3*p.size/16,fun _ _=>by constructor <;> linarith [p.size_pos]⟩
  have he : 0<volume A:=(isOpen_set_pi finite_univ fun _ _=> isOpen_Ioo).measure_pos _ h
  exact ENNReal.toReal_pos (he.trans_le (measure_mono (show A⊆p.Box from fun x hx=>⟨fun i=>(hx i (mem_univ _)).1.le,fun i=>(hx i (mem_univ _)).2.le⟩))).ne' p.compact_box.measure_ne_top

def coord (x : Cover) := p.spacing • WithLp.toLp 2 (fun i=>(x i : ℝ))
variable {n : ℕ}
def rel (x : Fin n→Cover) (c : Four ℝ) : Points n:= points fun i=> p.coord (x i)-WithLp.toLp 2 c
def termView (t : Test n) (x : Fin n→Cover) : (Four ℝ → ℂ):= fun c=> t (p.rel x c)
lemma term_integrable (t : Test n) (x) : IntegrableOn (p.termView t x) p.Box:= ContinuousOn.integrableOn_compact p.compact_box (Continuous.continuousOn (Continuous.comp t.continuous (PiLp.continuous_toLp 2 _|>.comp (continuous_pi fun _=> continuous_const.sub (PiLp.continuous_toLp 2 _)))))

-- complex linear tests only, no periodicization error assumed.
def smear (x : Fin n→Cover) : Test n→ₗ[ℂ] ℂ where
  toFun t := p.vol⁻¹ • ∫ c in p.Box, p.termView t x c
  map_add' a b:=by
    simp_rw [show p.termView (a+b) x=p.termView a x+p.termView b x from rfl]; rw [integral_add' (p.term_integrable a x) (p.term_integrable b x),smul_add]
  map_smul' z a:=by
    simp_rw [show p.termView (z • a) x = z • p.termView a x from rfl]; simp only [Pi.smul_apply]; rw [integral_smul (𝕜:=ℂ),RingHom.id_apply,smul_comm]

/-- We use a formula on top *torus* sites; for compact tests with clearance
this agrees with summing over the top cover (center included). -/
def Fits (s : Set (Points n)) := ∀ x∈s, ∀ i j, |x i j| ≤ p.size/16
theorem cover_window {s : Set (Points n)} (hf : p.Fits s) {c : Four ℝ} (hc : c∈p.Box) {x : Fin n→ Cover} (h : p.rel x c∈s) : ∀ i, lift (wrap p.p.side (x i))=x i := by
  intro i; refine lift_eq_iff.mpr ⟨rfl,fun j=>?_⟩
  have ht:=abs_le.mp (hf _ h i j); rcases hc with ⟨ha,hb⟩
  specialize ha j; specialize hb j; change p.size/8 ≤ c j at ha; change c j≤p.size/4 at hb; change -(_/16) ≤ p.spacing * (x i j:ℝ) - c j ∧ p.spacing * (x i j:ℝ)-c j≤ _/16 at ht; unfold size at *
  have he: -(p.p.side.val:ℝ)<2*(x i j:ℝ)∧2*(x i j:ℝ) ≤ p.p.side.val:=by
    have h:=p.positive;have hv := p.size_pos; unfold size at hv; constructor <;> nlinarith [ht.1,ht.2]
  exact_mod_cast he

theorem cover_zero {c : Four ℝ} (t : Test n) (h : p.Fits (tsupport t)) (hc : c∈p.Box) (x : Fin n→ Cover) (i : Fin n) (he: lift (wrap p.p.side (x i))≠x i) : p.termView t x c=0 := by unfold termView; apply image_eq_zero_of_notMem_tsupport; exact fun hx=> he (p.cover_window h hc hx i)
end Mesh
end YM.XSpace
