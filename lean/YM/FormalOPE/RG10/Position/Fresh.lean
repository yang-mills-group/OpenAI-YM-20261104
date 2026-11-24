import YM.FormalOPE.RG10.Position.OrbitSeat

/-!
The **actual leading proof inside lattice PT**, all separated (not actual Wilson-law
comparisons!). Include `Floral` at instance use. `Profile` with complex test means take REAL
output here at real basis (suitable for position tests). -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Position
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  InversionTop Orb LatticePT Lattice Mixed Source Gauge Precision FlatFeed PowerSeries
  Topology Physical.Profile PertExtension.Physical PertExtension.Position
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {F : Frames G} {d k n : ℕ}
    (H : Hol G) (S : ∀ d, SectionData (F.level d)) (hS : ∀ d, (S d).Sound H) (hp : ∀ d, Bid.pop (S d))
variable (U : Loft F) (u : Fin n → Deck F d)
-- limit statements even if q meets only hq; bulk asymptotic delivery chooses from the stipulated controllers, not all q.
variable (q:ℕ+)
local notation "σ" => Deck.token F d ∘ u
lemma highAdheres (i : Deck F d) : writes F d (deck F d i)=writes F (Deck.token F d i).1 (owner (Deck.token F d i)):= by
  rw [deckAt, written]; unfold owner; rw [deckAt, written]; rfl
lemma fervor (hh : U.Level F) (x:Points n) : Wick.moment G x (fun i=>writes F d (deck F d (u i))) =
    ∑ Z:(∀ i,Library (σ i)),(↑(∏ i,inkAt U (σ i) (Z i)):ℂ)*electricity (fun i=>enroll H S hS hp (σ i) (Z i)) x := by
  have he (i:Fin n) : writes F d (deck F d (u i))=∑ j:Library (σ i), (↑(inkAt U (σ i) j):ℂ) • electrical (enroll H S hS hp (σ i) j):= (highAdheres (u i)).trans (Eq.symm (against _ _ _ _ _ hh _))
  simp_rw [he]; rw [MultilinearMap.map_sum]; apply Finset.sum_congr rfl
  intro i _; rw [MultilinearMap.map_smul_univ]; push_cast; rfl
private abbrev heartbeat (t:Test n): Points n→ ℝ:=Complex.re ∘ t
lemma ostinate {x:Points n} (hx:x∈conf n) : (Wick.moment G x (fun i=>writes F d (deck F d (u i)))).im=0 := by
  apply Complex.conj_eq_iff_im.mp; change star (Wick.moment G x (fun i=>writes F d (deck F d (u i))))=_
  rw [← wick_bar hx]; apply congr_arg; funext i; rw [← writes_bar (h:=table_spin F), deck_real]
lemma vision (t:Test n):
    Physical.free (L:=YM.Maxwell.standard F) (deck F d) ⟨⟨n,t⟩,u⟩ =
    ∫ x:Points n, heartbeat t x * (Wick.moment G x (fun i=>writes F d (deck F d (u i)))).re := by
  unfold Physical.free Physical.reading readingC Test.applyTo; dsimp only -- inspect
  change Complex.re (∫ x:Points n,t x*(freeTable F).useAt (freeTable F) (1 • x) (fun i=>⟨d,deck F d (u i)⟩))= _
  simp_rw [one_smul,writes_eval]
  let K:=fun x:Points n=>Wick.moment G x (fun i=>writes F d (deck F d (u i)))
  refine (integral_re (t.smearing (K:=K) (fun x hx=>(Wick.moment_smooth (G:=G) _ hx).continuousAt.continuousWithinAt))).symm.trans ?_
  apply integral_congr_ae; filter_upwards with x; by_cases h:x∈conf n
  · unfold heartbeat; dsimp only [Function.comp_apply]; change Complex.re (t x * Wick.moment G x _)=_; rw [Complex.mul_re,ostinate u h,mul_zero,sub_zero]
  simp_rw [heartbeat,Function.comp_apply,t.vanishes h]; simp

lemma tending (t:Test n) (hh : U.Level F) (hq : 1<q.val) :
    Tendsto (fun m=>constantCoeff (prelude H S hS hp U σ q m (fun z=> heartbeat t (YM.points z))))
      atTop (𝓝 (Physical.free (L:=YM.Maxwell.standard F) (deck F d) ⟨⟨n,t⟩,u⟩)) := by
   let p:=heartbeat t
   have hts:Function.support p ⊆ tsupport t := fun y hy=> subset_closure (fun h=>hy (by simp only [p,heartbeat,Function.comp_apply,h, Complex.zero_re]))
   let U' (Z:∀ i,Library (σ i)): Fin n→ LatticePT.Word G := fun i=>enroll H S hS hp (σ i) (Z i)
   have HZ Z:=CutoffFree.profile_limit (U' Z) q hq p t.hasCompactSupport t.tsupport_subset hts (Complex.continuous_re.comp t.continuous)
   let c(Z:∀ i,Library (σ i)) := ∏ i,inkAt U (σ i) (Z i)
   have he:= tendsto_finsetSum (univ (α:=∀ i,Library (σ i))) fun Z _=> (HZ Z).2.const_mul (c Z)
   rw [vision]
   have hi : (fun x : Points n=> heartbeat t x * (Wick.moment G x (fun i=>writes F d (deck F d (u i)))).re) = fun x=> ∑ Z, c Z * CutoffFree.realTyped (U' Z) p x := by
     funext x; rw [fervor H S hS hp U u hh,Complex.re_sum,Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; unfold c p U' CutoffFree.realTyped; ring -- ofReal_mul_re
   apply he.congr' ?_ |>.mono_right (le_of_eq ?_)
   · filter_upwards with j; unfold prelude; simp_rw [map_sum,map_mul,constantCoeff_C,← coeff_zero_eq_constantCoeff_apply,coeff_mk]; apply Finset.sum_congr (by congr 1; apply Subsingleton.elim); intro i _; rfl
   congr 1; rw [hi,integral_finsetSum];
   · apply Finset.sum_congr rfl; intro k _; rw [integral_const_mul]
   exact fun i _=> ((HZ i).1).const_mul _
end YM.FormalOPE.RG10.Position
