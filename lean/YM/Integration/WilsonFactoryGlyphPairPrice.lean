import YM.Integration.WilsonFactoryPhysicalGlyphs

/-! A finite norm fixed by the supplied independent physical basis. There
is no reporting-scale loss in the transfer from two physical comparator
tests to the genuine finite matrix of joint marked Wilson errors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFactoryGlyphPairPrice
open Function Finset Wilson Lattice Labels RG Spec OPE SharpGram RG12 RG17 MS MS.Theater MS.Menus MS.Local.Physical
open MeasureTheory PhysicalNext.Repeat.Legato WilsonFactoryPhysicalGlyphs
open scoped Classical Topology BigOperators
variable {G : Gauge} (B : Deck G) (d : ℕ) (P : Frames G)

def chart : (Maxwell.freeTable P).Field d →L[ℂ] (Glyph B d → ℂ) :=
  LinearMap.toContinuousLinearMap ((WilsonFactoryOnShellGlyphs.spectrum B d).comp (Pert.RawLabels.physicalLabel P d))
def fee : ℝ := (Fintype.card (Glyph B d) : ℝ) * ‖chart B d P‖

theorem tariff (a : (Maxwell.freeTable P).Field d) :
    ∑ q : Glyph B d, ‖WilsonFactoryOnShellGlyphs.spectrum B d (Pert.RawLabels.physicalLabel P d a) q‖ ≤
      fee B d P * ‖a‖ := by
  change (∑ q : Glyph B d, ‖chart B d P a q‖) ≤ _
  calc
    _ ≤ ∑ _q : Glyph B d, ‖chart B d P‖ * ‖a‖ :=
      sum_le_sum fun q _ => (norm_le_pi_norm (chart B d P a) q).trans ((chart B d P).le_opNorm a)
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul,fee,mul_assoc]

variable {C : Family G} {S : Table C.book} (J : ℝ → PhysMS.tower S) (e : ℕ)
    (r s : ℝ) (a : (Spin.comparator C.book).Field d) (b : (Spin.comparator C.book).Field e)
    (N p : ℕ) (x y : Site (C.side N p)) (ζ : Config G (C.side N p) → ℂ)

def joint (q : Glyph B d) (t : Glyph B e) : ℂ :=
  C.omega N p (fun U => mark (C:=C) d J r (note (C:=C) B d q) N p x U *
      (mark (C:=C) e J s (note (C:=C) B e t) N p y U * ζ U))

def bill (A : Glyph B d → Glyph B e → ℂ) :=
  ∑ q : Glyph B d,∑ t : Glyph B e, ‖joint B d J e r s N p x y ζ q t - A q t‖

def trial (A : Glyph B d → Glyph B e → ℂ) :=
  ∑ q : Glyph B d,weight (C:=C) B d a q • ∑ t : Glyph B e, weight (C:=C) B e b t • A q t

theorem debit (good : Continuous ζ) (A : Glyph B d → Glyph B e → ℂ) :
    C.omega N p (fun U => mark (C:=C) d J r a N p x U * (mark (C:=C) e J s b N p y U * ζ U)) -
        trial (C:=C) B d e a b A =
    trial (C:=C) B d e a b (fun q t => joint B d J e r s N p x y ζ q t - A q t) := by
  rw [WilsonFactoryPhysicalGlyphs.joint B d J r a N p x s b y ζ good]
  simp only [trial,joint,smul_sub,Finset.sum_sub_distrib]

theorem priced (good : Continuous ζ) (A : Glyph B d → Glyph B e → ℂ) :
    ‖C.omega N p (fun U => mark (C:=C) d J r a N p x U * (mark (C:=C) e J s b N p y U * ζ U)) -
      trial (C:=C) B d e a b A‖ ≤
      (fee B d C.labels * ‖a‖) * (fee B e C.labels * ‖b‖) * bill B d J e r s N p x y ζ A := by
  let H := joint B d J e r s N p x y ζ
  let M := bill B d J e r s N p x y ζ A
  have hnon : 0≤M := sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  have each (q : Glyph B d) (t : Glyph B e) : ‖H q t - A q t‖ ≤ M := by
    exact (single_le_sum (f:=fun l => ‖H q l-A q l‖) (fun _ _ => norm_nonneg _) (mem_univ t)).trans
      (single_le_sum (f:=fun h => ∑ l,‖H h l - A h l‖) (fun _ _ => sum_nonneg fun _ _ => norm_nonneg _) (mem_univ q))
  have hr (q : Glyph B d) :
      ‖∑ t : Glyph B e, weight (C:=C) B e b t • (H q t - A q t)‖ ≤ (fee B e C.labels * ‖b‖) * M := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_smul]
    exact (sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (each q t) (norm_nonneg _)).trans
      (by rw [←Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (tariff B e C.labels b) hnon)
  rw [debit B d J e r s a b N p x y ζ good A]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_smul]
  have hp : 0 ≤ fee B e C.labels * ‖b‖ * M := mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ContinuousLinearMap.opNorm_nonneg _)) (norm_nonneg _)) hnon
  calc
    _ ≤ ∑ q : Glyph B d, ‖weight (C:=C) B d a q‖ * (fee B e C.labels * ‖b‖ * M) :=
      sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hr q) (norm_nonneg _)
    _ ≤ (fee B d C.labels * ‖a‖) * (fee B e C.labels * ‖b‖ * M) := by
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (tariff B d C.labels a) hp
    _ = _ := (mul_assoc _ _ _).symm

end YM.Integration.WilsonFactoryGlyphPairPrice
