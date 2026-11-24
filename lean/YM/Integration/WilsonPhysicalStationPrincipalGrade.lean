import YM.Integration.WilsonPhysicalStationFactoryGerm

/-! Exact equal-engineering response of the dated original triangular headings.
A homogeneous input is kept unscaled throughout the intervening march. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationPrincipalGrade
open Function Filter Labels RG Wilson Source Lattice Bid Extra.Histories Next.Rank Next.Rank.East Next.Rank.Price
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph WilsonPhysicalStationFactoryGerm
open Work.G08 Next.Foundations
open scoped Classical BigOperators
variable {G:Gauge}{d:ℕ}{F:Frame G d}
def through (T:Heading F) (fine coarse:ℝ):Prop := ∀a b:F.Index,
    (F.grades b).1 ≤ (F.grades a).1 → T.map (Size.axis F a) b =
      if b=a then ((coarse/fine:ℝ):ℂ)^(F.grades a).2 else 0
def above (w:ℕ)(v:F.Coeff):Prop := ∀a,(F.grades a).1 < w → v a=0

theorem one (T:Heading F){fine coarse:ℝ}(price:through T fine coarse)
    (L:Side){w:ℕ}{v:F.Coeff}(start:above w v)(b:F.Index)(hb:(F.grades b).1 ≤ w):
    T.leads L v b = (((coarse/fine:ℝ):ℂ)^(F.grades b).2)*((L.val:ℂ)^(d-(F.grades b).1))*v b := by
  classical
  have form:T.leads L v b=∑a:F.Index,
      (v a*(L.val:ℂ)^(d-(F.grades a).1))*T.map (Size.axis F a) b := by
    change T.map (vowel F L v) b=_
    conv_lhs => rw [← Size.sum_axes F (vowel F L v)]
    simp [map_sum,Finset.sum_apply,map_smul,Pi.smul_apply,smul_eq_mul,vowel,mul_comm]
  rw [form,Finset.sum_eq_single b]
  · rw [price b b le_rfl,if_pos rfl];ring
  · intro a _ ha
    by_cases small:(F.grades a).1 < w
    · rw [start a small];ring
    · rw [price a b (hb.trans (le_of_not_gt small)),if_neg ha.symm];ring
  · simp

theorem stays (T:Heading F){fine coarse:ℝ}(price:through T fine coarse)
    (L:Side){w:ℕ}{v:F.Coeff}(start:above w v):above w (T.leads L v) := by
  intro b hb
  rw [one T price L start b hb.le,start b hb,mul_zero]

variable (R:Run G)(d:ℕ)
local notation "F₀" => R.family.labels.level d
local notation "a₀" => R.family.S.a
local notation "τ" => (fun i:ℕ=>(R.family.path.levels.budget i).threshold)
def march (T:ℕ→Heading F₀) (i:ℕ):(ℕ → (F₀).Coeff→(F₀).Coeff)
  | 0 => id
  | n+1 => fun v=> march T i n ((T (i+n)).leads (R.family.S.block (i+n)) v)

theorem original (T:ℕ→Heading F₀)(i n:ℕ)
    (book:∀k,i ≤ k→k < i+n→through (T k) ((τ) (k+1)) ((τ) k))
    {w:ℕ}{v:(F₀).Coeff}(start:above w v)(b:(F₀).Index)(hb:((F₀).grades b).1 ≤ w):
    march R d T i n v b=
      ((((τ) i/(τ) (i+n):ℝ):ℂ)^((F₀).grades b).2)*
      ((((a₀) i/(a₀) (i+n):ℝ):ℂ)^(d-((F₀).grades b).1))*v b := by
  induction n generalizing v with
  | zero => simp [march,(R.family.path.levels.budget i).threshold_pos.ne', (R.family.S.a_pos i).ne']
  | succ n ih =>
    let k := i+n
    have price:through (T k) ((τ) (k+1)) ((τ) k) := book k (Nat.le_add_right ..) (Nat.lt_succ_self _)
    have hg (m:ℕ):((τ) m:ℂ)≠0 := by exact_mod_cast (R.family.path.levels.budget m).threshold_pos.ne'
    change march R d T i n ((T k).leads (R.family.S.block k) v) b=_
    rw [ih (fun j hj hk=>book j hj (by omega)) (stays (T k) price _ start),
       one (T k) price _ start b hb]
    change _ = ((((τ) i/(τ) (k+1):ℝ):ℂ)^_) * ((((a₀) i/(a₀) (k+1):ℝ):ℂ)^_) * v b
    have opt:((((a₀) i/(a₀) (k+1):ℝ):ℂ))=(((a₀) i/(a₀) k:ℝ):ℂ)*((R.family.S.block k).val:ℂ) := by
      rw [R.family.S.a_step k]; push_cast; simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]; ring
    have thermal:((((τ) i/(τ) (k+1):ℝ):ℂ))=(((τ) i/(τ) k:ℝ):ℂ)*(((τ) k/(τ) (k+1):ℝ):ℂ) := by
      push_cast; field_simp [hg k]
    rw [opt,thermal,mul_pow,mul_pow]
    change _=_
    dsimp only [k]
    ring

end YM.Integration.WilsonPhysicalStationPrincipalGrade
