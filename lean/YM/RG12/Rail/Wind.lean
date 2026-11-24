import YM.MergeProof.West.Esme
import YM.Pert.Scale.Engineering
/-!
# Mural-Ray compactification for true supplies

The k comparators (stamping mass `earning`) are stated in the seed at compact
separated configurations in loom units. Can we take the larger configurations
needed to compare across lamp sizes (L not bounded)? Yes, expose receipt calculus
and pass to joint limits of inverse shape diameter in the free pricing inputs.
No changing or assuming any Poised premises or station commissioning.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Rail
open Function Set Filter Lattice RG Next.Rank Next.Rank.Atlas Maxwell Labels MeasureTheory
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {C:Family G}{d k n v : ℕ}
variable {a : Points n} (ha:a∈conf n)
def Anemos (a:Points n) (R:ℝ)(x : Points n) := ∃ t:ℝ, t∈Icc 1 R ∧ x=t • a
/-- Can test claims indexed on all stations uniform on Anemos by passing to a subsequence with
inverse length limit, even if the row itself NOT precompact. In a richer compact set of clear
shapes, also pass to a sub-subsequence in shape. -/
lemma scope {B:ℕ→Points n→ Prop}{Z:ℕ→Points n→Points n}{R:ℕ→ℝ}
    (hb:∀ f:ℕ→ℕ,Tendsto f atTop atTop→∀ (x:ℕ→Points n)(t:ℕ→ℝ),(∀ i,1≤ t i ∧ t i ≤ R (f i))→(∀ i,Z (f i) (x i)= t i • a)→∀ u:ℝ,Tendsto (fun i=> (t i)⁻¹) atTop (𝓝 u) → ∀ᶠ i in atTop,B (f i) (x i)):
      ∀ᶠ k in atTop,∀ x:Points n,Anemos a (R k) (Z k x)→ B k x:=by
   by_contra! h -- frequent
   have hh (i:ℕ): ∃ k≥i,∃ x,Anemos a (R k) (Z k x)∧¬B k x:= by
      by_contra! he; have he': ∀ᶠ k in atTop, ∀ x,Anemos a (R k) (Z k x)→ B k x:= eventually_atTop.2 ⟨i,he⟩
      obtain ⟨b,hv,p,ht,hx⟩:= (he'.and_frequently h).exists -- check
      exact hx (hv p ht)
   choose f H x hA hp using hh
   choose t ht hs using hA
   let y(i):=(t i)⁻¹
   obtain ⟨u,hu,p,hp',hv⟩:=isCompact_Icc.isSeqCompact (s:=Icc (0:ℝ) 1) (x:=y) (fun i=> by have hx:1 ≤ t i := (ht i).1; exact Set.mem_Icc.mpr ⟨by unfold y; positivity, inv_le_one_of_one_le₀ hx⟩)
   have he: Tendsto f atTop atTop:= tendsto_atTop_mono H tendsto_id
   obtain ⟨j,hj⟩:= (hb (f ∘ p) (he.comp hp'.tendsto_atTop) (x ∘ p) (t ∘ p) (fun i=>ht (p i)) (fun i=>hs (p i)) u hv).exists
   exact hp (p j) hj
open Pert.Scale
-- one operator and its occurrence list can be of ANY fixed horizon
private lemma wind {q p:Maxwell.Slot G}{x y:E4}(h:x≠y){t:ℝ}(ht:1 ≤ t): Wick.entry p q (t • x) (t • y)= ((t⁻¹:ℝ):ℂ)^(Extra.FD.costKey p+Extra.FD.costKey q) * Wick.entry p q x y:=by
    have Ht:= (zero_lt_one.trans_le ht).ne'
    have he:=bit_stretch (t:=t) p q h Ht
    rw [Complex.ofReal_inv,inv_pow,← he,← mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Ht)),one_mul]
lemma across {t:ℕ→ℝ}{p q:Maxwell.Slot G}{x y:E4}(h:x≠y)(ht:∀ i,1 ≤ t i){x₀:ℝ}(hx:Tendsto (fun i=>(t i)⁻¹) atTop (𝓝 x₀)): ∃ a, Tendsto (fun i=> Wick.entry p q (t i • x) (t i • y)) atTop (𝓝 a):=by
    simp_rw [wind h (ht _)]
    exact ⟨_, ((Complex.continuous_ofReal.continuousAt.tendsto.comp hx).pow _).mul_const _⟩
-- two things: Roll and Key analyses, unbounded but separated. First readsEach
open Next.Rank.Configuration
include ha
lemma pair_wind (p q: Fin n×KeyIn G d)(t:ℕ→ℝ)(ht:∀ i,1≤ t i){x₀:ℝ}(hx:Tendsto (fun i=>(t i)⁻¹) atTop (𝓝 x₀)): ∃ u,Tendsto (fun i=> readsEach G d p q (t i • a)) atTop (𝓝 u):=by
   have he(p q: Fin n×Maxwell.Slot G): ∃ u:ℂ,Tendsto (fun i=>pointwise (t i • a) p q) atTop (𝓝 u):=by
      classical
      unfold pointwise; by_cases hp:p.1=q.1
      · simp only [if_pos hp]; exact ⟨0,tendsto_const_nhds⟩
      simp only [if_neg hp]; exact across ((ha:Injective a.ofLp).ne hp) ht hx
   choose y hY using he
   unfold readsEach; simp only [Finsupp.linearCombination_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
   exact ⟨_, tendsto_finsetSum _ (fun i _=> tendsto_const_nhds.mul (tendsto_finsetSum _ (fun j _=> tendsto_const_nhds.mul (hY j i))))⟩
-- profile covers markers with mixed horizon. pass to limit by Mag formal Wick evaluation
open Wick Marker Extra.FD
omit ha
lemma wind_mom {x:Points v}(h:x∈conf v)(t:ℕ→ℝ)(ht:∀ i,1 ≤ t i){x₀:ℝ}(hx:Tendsto (fun i=>(t i)⁻¹) atTop (𝓝 x₀))(P:Fin v→ WickPol G):∃ z,Tendsto (fun i=>moment G (t i • x) P) atTop (𝓝 z):=by
   have hc(U:Powers G v) : ∃ z:ℂ,Tendsto (fun i=> monomial (t i • x) U) atTop (𝓝 z):=by
      let V:= ∑ i,Finsupp.weight costKey (U i)
      have he(i): monomial (t i • x) U=((↑((t i)⁻¹):ℂ)^V)*monomial x U:=by
         have hf:= (zero_lt_one.trans_le (ht i)).ne'
         rw [← circuit U h (t:=t i) hf,← mul_assoc, Complex.ofReal_inv, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hf)),one_mul]
      simp_rw [he]; exact ⟨_, ((Complex.continuous_ofReal.continuousAt.tendsto.comp hx).pow _).mul_const _⟩
   choose z hz using hc
   simp_rw [sumFormula] -- test
   exact ⟨_, tendsto_finsetSum _ (fun i _=>tendsto_const_nhds.mul (hz _))⟩
open Glyph Cells
lemma profile_wind (a:Points n)(ha:a∈conf n) (t:ℕ→ℝ)(ht:∀ i,1 ≤ t i){x₀:ℝ}(hx:Tendsto (fun i=>(t i)⁻¹) atTop (𝓝 x₀))(B:Fin n→(Cells.standard C).Tag):∃ v, Tendsto (fun i=> Read.maxProfile C (t i • a) B) atTop (𝓝 v):=by
    have he (r:modes (Fin n)): ∃ z:ℂ, Tendsto (fun i=> (Read.maxProfile C (t i • a) B).part r) atTop (𝓝 z):=by
       unfold Read.maxProfile
       simp_rw [Read.profile_part]
       let g:ℕ→ℂ:= fun i=> (freeTable C.labels).useAt (freeTable C.labels) (Read.portion r (t i • a)) (fun j=> B (Read.project r j).val)
       change ∃ z:ℂ, Tendsto g _ _; unfold g
       simp_rw [Extra.FD.writes_eval,show ∀ i:ℕ, Read.portion r (t i • a)=t i • Read.portion r a from fun i=>by rfl]
       exact wind_mom (Read.portion_free r a ha) t ht hx _
    choose z hz using he
    exact ⟨Poly.inject z,tendsto_pi_nhds.mpr hz⟩
end YM.RG12.Rail
