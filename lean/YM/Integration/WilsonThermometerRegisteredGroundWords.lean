import YM.Integration.WilsonThermometerInversionMaxwell
import YM.Integration.WilsonMaxwellThermometerGroundInversion

/-! The native zero-order term of a restored socket word as a finite
sum of Wick moments on the original placed plaquettes and colors. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredGroundWords
open Function Finset MeasureTheory Lattice Wilson RG Gauge Source Labels PhysicalNext.Repeat.Legato
open PertExtension PertExtension.Chart PertExtension.Orb PertExtension.Series PertExtension.Series.Radial
open PertExtension.LatticePT PertExtension.GaussianScore Next.Rank.Normal
open WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds WilsonThermometerInversionHead
open scoped Classical BigOperators ContDiff Topology
variable {G:Gauge} (R:Run G) {V T:Type} [Fintype V] (d:V→ℕ)
variable (b:(j:V)→Choice R d j) (place:V→Fin 3) (sites:Fin 3→Lattice.Cover) {n:Side}
local notation "e" j:max => WilsonThermometerDeclaredSeeds.entry R d j (b j)
abbrev Colors := (j:V)→Fin (rank R d (e j))→G.ColorIndex
abbrev Words := (j:V) × Fin (rank R d (e j))
def cash (a:Colors R d b) : ℝ :=
  ∏j:V,if pole R d (e j)=rank R d (e j) then (raw R d (e j)).coeff (a j) else 0
def tag (a:Colors R d b) (l:Words R d b) : WilsonMaxwellThermometerGroundInversion.Entry G :=
  (place l.1,((raw R d (e l.1)).leg l.2,a l.1 l.2))

omit [Fintype V] in
private theorem component (j:V) (z:Site n) (u:Dir G n) :
    selected R d (e j) z u =
      ∑a:Fin (rank R d (e j))→G.ColorIndex,
        (if pole R d (e j)=rank R d (e j) then (raw R d (e j)).coeff a else 0) *
          ∏k:Fin (rank R d (e j)),Slope.leg z ((raw R d (e j)).leg k,a k) u := by
  by_cases h:pole R d (e j)=rank R d (e j) <;> simp [selected,h,polar]

theorem expanded (u:Dir G n) :
    ∏j:V,selected R d (e j) (wrap n (sites (place j))) u =
      ∑a:Colors R d b,cash R d b a * ∏l:Words R d b,
        Slope.leg (wrap n (sites (tag R d b place a l).1)) (tag R d b place a l).2 u := by
  simp_rw [component R d b]
  rw [Fintype.prod_sum]
  refine sum_congr rfl (fun a _=>?_ )
  rw [prod_mul_distrib,Fintype.prod_sigma]
  rfl

variable (g τ:ℝ) (v:(j:V)→R.family.label (d j)) (t:V→T→ℂ) (x:T) (L:ℂ→L[ℝ]ℝ)
local notation "c" => L (∏j:V,t j x * scalar R d g τ v (e j))
local notation "O" => WilsonThermometerInversionSockets.word R d univ b (fun j=>wrap n (sites (place j))) g τ v t x L
local notation "w" => WilsonThermometerInversionSockets.charge R d univ b
local notation "read" a:max => fun l:Words R d b=>Slope.leg (wrap n (sites (tag R d b place a l).1)) (tag R d b place a l).2

theorem original (ev:Even n.val) :
    (↑(Orb.diag (restrictedO (O)) (w)):ℂ) =
      ∑a:Colors R d b, ↑((c)*cash R d b a)*
        blend (WilsonMaxwellThermometerGroundInversion.earned ev sites) 0
          (glyphs (tag R d b place a) univ) := by
  have fee (a:Colors R d b) : Integrable (fun u:Dir G n=>
      (((c)*cash R d b a)*(∏l:Words R d b,(read a) l u))*kernel fiscal u)
      (tangent G (Cotree n)) := by
    have h:=(saddle (G:=G) ev).integrable_entry (tangent G (Cotree n))
      (Law.product_bound (read a) univ) (Law.product_cont (read a) univ)
    rw [←saddleLaw ev] at h
    simpa only [Law.product,Pi.mul_apply,mul_assoc] using h.const_mul ((c)*cash R d b a)
  rw [WilsonThermometerInversionMaxwell.ground R d univ b (fun j=>wrap n (sites (place j))) g τ v t x L ev]
  simp_rw [expanded R d b place sites,Finset.mul_sum,Finset.sum_mul]
  rw [integral_finsetSum]
  · rw [Finset.sum_div,Complex.ofReal_sum]
    apply sum_congr rfl;intro a _
    have eq := WilsonMaxwellThermometerGroundInversion.original (G:=G) ev sites (tag R d b place a) univ
    rw [←eq,←Complex.ofReal_mul]
    congr 1
    unfold Orb.gaussian Law.average
    rw [←saddleLaw ev]
    simp_rw [mul_assoc,integral_const_mul,mul_div_assoc,Pi.mul_apply]
  · intro a _
    simpa only [mul_assoc] using fee a

end YM.Integration.WilsonThermometerRegisteredGroundWords
