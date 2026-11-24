import YM.RGComparison01.Hires
import YM.RGComparison01.Selectors

/-!
# Stencil budgets after separating both selectors

 E reanchoring before Orientation. Labels themselves preserved; may
 later consume via exact Marquee movement. The selectors share one
 workspace @ genuine `X: Match`: in this version work with `staple` self. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Divides
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Opacity
open PhysicalNext PhysicalNext.Repeat Height Song Brim Beam
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Selector
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G}
    {T : Tube G S} {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ}
    {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f} {μ q C' d v Y A b r B s α a i : ℝ}
    {k j n ℓ : ℕ} {χ : Chi} {H : Cash W s μ L Q o α T R}
variable (p : BudgetPoint)
    (N : Captain H j C' d v Y A b r B q k χ)

abbrev selfA (H : Cash W s μ L Q o α T R) : Match.Alliance H H 1 0 := Match.staple rfl rfl rfl

@[simp] lemma farther (i : H.fragrances) : (selfA H).furrow i=i := by cases i; rfl

/-- Family embedded on left of the Magazine up to selector -/
def bySong (M : Magazine H→Prop) (χ : Chi) (γ : ℝ) (z : Magazine H) : Config G c→ℝ :=
    if M z then opus H (selfA H) χ γ z else 0

def byLog (M : H.fragrances→Prop) (χ : Chi) (z : H.fragrances) :=
    if M z then Song.sequence H (selfA H) χ z else 0

lemma atLog (M:Magazine H→Prop) (χ : Chi) (γ:ℝ) : (bySong M χ γ) ∘ Sum.inl = byLog (M ∘ Sum.inl) χ:= by
  funext i; unfold byLog bySong; simp only [Function.comp_apply]; split <;> rfl

lemma bookLog {price : ℝ} (Sel : H.fragrances → Prop)
    (hp : p.threshold = Pressure.temp s) (hd : p.B = radiusB s)
    (hj : p.order ≤ j) (hn : p.power ≤ n) (hr : preExponent p ≤ a)
    (hQ : Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z => if Sel z then N.markΦ z n else 0) a price) :
    Meadow.Budget p (Beam.dashboard H) (byLog Sel χ) price := by
  let f i:= if Sel i then N.markΦ i n else 0
  have h i : p.Regular (Beam.dashboard H i).support (byLog Sel χ i) ∧ p.supBounds (Beam.dashboard H i).site
      (Beam.dashboard H i).support (byLog Sel χ i) (f i):= by
    unfold byLog f; split
    · have hk:= N.gloryBudget i p hp hj
      have he : (Beam.dashboard H i).support=Captain.reachability i := (Beam.see ..).trans ((farther (H:=H) i) ▸ reconnects H (selfA H) i)
      have ha := hk.2.2 n hn _ (show _ from he ▸ (Beam.dashboard H i).anchor)
      rw [he]
      have hv : Song.sequence H (selfA H) χ i= (-1:ℝ) • (fun V=> stream H χ V i) := by
        funext V; unfold Song.sequence; simp [farther]
      rw [hv]; have Hz := CouplingShape.sup_scale (-1) ha; rw [abs_neg,abs_one,one_mul] at Hz
      exact ⟨CouplingShape.reg_scale _ hk.2.1,Hz⟩
    exact ⟨CouplingShape.reg_const _,sup_le (CouplingShape.sup_const _) (abs_zero).le⟩
  refine ⟨f,fun x=> ?_,h⟩
  refine budget_mono (hQ x) (fun i=> ?_) (fun i=>?_)
  · split; next => exact mul_nonneg (h _|>.2.1) (Real.exp_nonneg _)
    exact le_rfl
  split
  next hx =>
    have he : (Beam.dashboard H i).support=Captain.reachability i := (Beam.see ..).trans ((farther (H:=H) i) ▸ reconnects H (selfA H) i)
    dsimp only
    rw [if_pos (show x∈Captain.reachability i from hx ▸ (he ▸ (Beam.dashboard H i).anchor)), he, hd]
    exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)))
      (h _|>.2.1)
  exact (hQ x).1 i

lemma loosen {a b : ℝ} {ι : Type} {R : ι→ RegularAddress c} {s:ι → Config G c→ℝ} (h : Meadow.Budget p R s a) (hp:a ≤ b) :
    Meadow.Budget p R s b := by obtain ⟨f,hf,hT⟩:=h; exact ⟨f,fun i=>budget_loosen (hf i) hp,hT⟩

lemma budgets_union {a b : ℝ} {Sel N : H.fragrances→Prop} (h : Meadow.Budget p (Beam.dashboard H) (byLog Sel χ) a)
    (he : Meadow.Budget p (Beam.dashboard H) (byLog N χ) b) :
    Meadow.Budget p (Beam.dashboard H) (byLog (fun z=>Sel z ∨ N z) χ) (a+b) := by
  obtain ⟨f,h,hF⟩:=h; obtain ⟨g,hG,hV⟩:=he
  refine ⟨fun i=> f i+g i, fun i=> ?_,fun i=>?_⟩
  · convert budget_plus (h i) (hG i) using 1; ext u; by_cases hn:(Beam.dashboard H u).site=i <;> simp [hn,add_mul]
  by_cases hv : Sel i
  · rw [show byLog (fun z => Sel z ∨ N z) χ i=byLog Sel χ i by unfold byLog; simp [hv]]
    exact ⟨(hF i).1, VerifiedReset.sup_le (hF i).2 (le_add_of_nonneg_right (hV i).2.1)⟩
  rw [show byLog (fun z => Sel z ∨ N z) χ i=byLog N χ i by unfold byLog; simp [hv]]
  exact ⟨(hV i).1, VerifiedReset.sup_le (hV i).2 (le_add_of_nonneg_left (hF i).2.1)⟩

lemma reduced {δ : ℝ} (C : Magazine H→ Config G c→ℝ) (τ : ℝ) (D : Magazine H→ Config G c→ℝ)
    (N : Magazine H→Prop)
    (h : Meadow.Budget p (Beam.contents H p) C τ) (hx : Meadow.Budget p (Beam.contents H p) D δ) :
    Meadow.Budget p (Beam.contents H p) (fun i=> if N i then C i else D i) (τ+δ) := by
  obtain ⟨f,h,hF⟩:= h; obtain ⟨g,hG,hV⟩:=hx
  refine ⟨fun i=> f i+g i, fun i=> ?_,fun i=>?_⟩
  · convert budget_plus (h i) (hG i) using 1; ext u; by_cases hn:(Beam.contents H p u).site=i <;> simp [hn,add_mul]
  by_cases hv : N i
  · simp only [hv, ↓reduceIte]; exact ⟨(hF i).1,sup_le (hF i).2 (le_add_of_nonneg_right (hV i).2.1)⟩
  simp only [hv, ↓reduceIte]; exact ⟨(hV i).1,sup_le (hV i).2 (le_add_of_nonneg_left (hF i).2.1)⟩

-- The sharp singleton part of Inherited, limit O(1/L) before turnFee.
lemma principal (p : BudgetPoint) {κ q' : Chi} {δ K t z : ℝ} {D : JointLoad.Heir.Record} {Ω : ℕ → Prop}
    (hp : p.B=radiusB s) (ht : preExponent p ≤ t) (hq : Brim.Hired H Ω D q' κ χ z p t K δ) :
    Meadow.Budget p (Beam.dashboard H) (byLog (fun i:H.fragrances=> (Inherited Ω i) ∧ ¬ Height.tired H i) χ) (K+δ) := by
  obtain ⟨⟨v,hv,Hv⟩,u,Hs,hs⟩:= hq
  let w i:= v i+u i; let e : ℕ ↪ H.fragrances:= ⟨Brim.icon H, Beam.icon_inj H⟩; let f z:= Function.extend e w 0 z
  let g (i:H.fragrances):= if (∃ k, Ω k ∧ i=e k ∧ ¬Height.tired H i) then f i else 0
  let Sel (i:H.fragrances) := (Inherited Ω i) ∧ ¬ Height.tired H i
  have hK i : p.Regular (Beam.dashboard H i).support (byLog Sel χ i) ∧ p.supBounds (Beam.dashboard H i).site
      (Beam.dashboard H i).support (byLog Sel χ i) (g i):= by
    unfold g; split
    next h =>
      obtain ⟨j,hj,rfl,h⟩:= h
      have he : Sel (e j):= ⟨⟨j,hj,none,Finset.mem_singleton_self _⟩,h⟩
      have hd := Beam.shall H j h
      rw [← hp,Brim.concern H] at hd
      unfold byLog f; rw [if_pos he,e.injective.extend_apply,show Beam.dashboard H (e j)= _ from Beam.impact H j,
        show Song.sequence H _ χ (e j)=announced H D q' κ z j-Brim.glyph H D q' κ χ z j from (by
          funext V; change (-1:ℝ) * stream H χ V ((selfA H).furrow (e j))=_- (stream H χ V (e j)+_); rw [farther]; ring)]
      exact ⟨CouplingShape.reg_sub (hv j hj).1 (hs j hj).1, CouplingShape.sup_sub (hv j hj).1 (hs j hj).1 (hv j hj).2 ((hs j hj).2 hd)⟩
    next hn =>
      rw [show byLog Sel χ i=0 by
        unfold byLog; split
        next hi =>
          funext V; change (-1:ℝ)*stream H χ V ((selfA H).furrow i)=0; rw [farther]
          by_cases hq : stream H χ V i=0; · rw [hq,mul_zero]
          obtain ⟨j,hj,hᵢ⟩:= Selector.minor_inherited hi.1 hi.2 V hq; exact (hn ⟨j,hj,hᵢ,hi.2⟩).elim
        rfl]
      exact ⟨CouplingShape.reg_const _, sup_le (CouplingShape.sup_const _) (abs_zero).le⟩
  refine ⟨g,fun x=>?_,hK⟩
  apply Beam.wallet e
  · refine budget_mono (budget_plus (Hv x) (Hs x)) (fun i=> ?_) (fun i=>?_)
    · split; next _ => exact mul_nonneg (hK _|>.2.1) (Real.exp_nonneg _)
      exact le_rfl
    dsimp only
    simp only [show Beam.dashboard H (e i)= _ from Beam.impact H i]
    split
    next hi =>
      apply le_trans (b:=g (e i)*Real.exp (t*coverNumber p.B (plate H i).support))
        (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _))) (hK _|>.2.1))
      unfold g f; split
      next _ => rw [e.injective.extend_apply]; unfold w; rw [add_mul]
      next _ =>
        rw [zero_mul]
        have ht:= (budget_plus (Hv x) (Hs x)).1 i; simpa only [hi, ↓reduceIte] using ht
    next hu => simp
  intro i hi; unfold g; split_ifs with h hx; exact (hi (by obtain ⟨j,-,hv,-⟩:=hx; exact ⟨j,hv.symm⟩)).elim; simp; rfl
end YM.RGComparison01.Divides
