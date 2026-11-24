import YM.Contacts.Terrain.Hulls
import YM.Contacts.Terrain.Trestle
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Fir
/-! # Per lantern early score. Does not assume itinerary or success of modelling. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Terrain
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Beam Stained Shield
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i n' γ : ℝ} {k j n ℓ : ℕ}
    (H : Cash W s μ L Q o α T R) {p : BudgetPoint} {χ : Chi}
namespace Cap
abbrev Budget := @Meadow.Budget
-- exposed tools
protected lemma add {ι:Type} {f h u:ι→ Config G c→ℝ} (he : u=f+h) {A: ι→RegularAddress c} (p : BudgetPoint)
   (hp : Meadow.Budget p A f a) (hv:Meadow.Budget p A h δ): Meadow.Budget p A u (a+δ):= by
  obtain ⟨k,h',hv'⟩:=hv; obtain ⟨c',hc,hF⟩:=hp; rw [he]; refine ⟨c'+k,fun i=> ?_,fun i=>?_⟩
  · convert budget_plus (hc i) (h' i) using 2 with x; dsimp only [Pi.add_apply]; split <;> ring
  have hh:(f+h) i=f i-((-1:ℝ) • h i):= by simp
  have hp:= CouplingShape.reg_sub (hF i).1 (CouplingShape.reg_scale (-1) (hv' i).1); rw [hh]; refine ⟨hp,?_⟩
  have hb:= CouplingShape.sup_scale (-1) (hv' i).2; rw [abs_neg,abs_one,one_mul] at hb; exact CouplingShape.sup_sub (hF i).1 (CouplingShape.reg_scale (-1) (hv' i).1) (hF i).2 hb
protected lemma raise {ι:Type} {f:ι→ Config G c→ℝ} {A: ι→RegularAddress c} {p : BudgetPoint}
   (hp : Meadow.Budget p A f a) (hv:a≤δ): Meadow.Budget p A f δ:= by obtain ⟨t,ht,h⟩:=hp; exact ⟨t,fun i=>budget_loosen (ht i) hv,h⟩
end Cap

def runway : Alliance H H 1 0 := staple rfl rfl rfl
lemma stale (i:H.fragrances) : (runway H).furrow i=i:= by
  cases i with | mk i z=> rfl
-- density commitments BEFORE orbit average
abbrev Make (p:BudgetPoint) (χ:Chi) (K:H.fragrances→Prop) (a:ℝ) := Meadow.Budget p (Beam.dashboard H) (fun i=>if K i then Song.sequence H (runway H) χ i else 0) a

lemma shed (p:BudgetPoint) (χ:Chi) (U V:H.fragrances→Prop) (hu:Make H p χ U a) (hv:Make H p χ V b) : Make H p χ (fun i=> U i ∨ V i) (a+b):= by
  have h:= Meadow.emptyFree _ p hv (fun i=> if U i then 0 else (if V i then Song.sequence H (runway H) χ i else 0)) (fun i=> by by_cases he:U i <;> simp [he])
  refine Cap.add ?_ p hu h
  funext i; dsimp only [Pi.add_apply]; by_cases hi:U i<;> simp [hi]
lemma nextK (p:BudgetPoint) (χ:Chi) (U V:H.fragrances→Prop) (hu:Make H p χ U a) (hv:∀ i,V i → ∀ x, stream H χ x i ≠0 → U i) : Make H p χ V a:= by
  refine Meadow.emptyFree _ p hu _ ?_; intro i; try dsimp only
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl
  · right; ext x; rw [Song.sequence, stale]; have he: stream H χ x i=0:= by_contra (fun h=> (by assumption : ¬U i) (hv i (by assumption) x h)); change (-1:ℝ)*stream H χ x i = 0; rw [he,mul_zero]
  exact Or.inl rfl

variable (p χ)
lemma frost (U:H.fragrances→Prop) (N : Captain H j C' d v Y A b r B q k χ) (hP:p.threshold=Pressure.temp s) (ht:p.B=radiusB s) (he: preExponent p ≤ a)
    (hw:p.order ≤ j) (hv:p.power ≤ n) {Ω:ℕ→ℝ} (η y:ℝ) (w:H.fragrances→Prop) (hx:∀ i, w i → η≤ efface H Ω i) (hy:0<η)
    (hF:Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z=> if U z then efface H Ω z * N.markΦ z n else 0) a y) : Make H p χ (fun i=> U i∧w i) (η⁻¹*y):= by
  let f i:= if U i∧w i then N.markΦ i n else 0
  let g i:= if U i∧w i then Song.sequence H (runway H) χ i else 0
  have h i : p.Regular (Beam.dashboard H i).support (g i) ∧ p.supBounds (Beam.dashboard H i).site (Beam.dashboard H i).support (g i) (f i):= by
    unfold f g; split
    · have hk:= N.gloryBudget i p hP hw
      rw [Song.sequence, stale, Beam.see]; have Hz:= CouplingShape.sup_scale (-1) (hk.2.2 n hv _ (show _ from (Beam.see H i) ▸ (Beam.dashboard H i).anchor)); rw [abs_neg,abs_one,one_mul] at Hz
      exact ⟨CouplingShape.reg_scale _ hk.2.1,Hz⟩
    exact ⟨CouplingShape.reg_const _,by simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=p) (X:=(Beam.dashboard H i).support) (o:=(Beam.dashboard H i).site) 0)⟩
  refine ⟨f,fun x=>?_,fun i=> by by_cases he:U i∧w i <;> simpa only [g,if_neg,if_pos,he,↓reduceIte] using h i⟩
  have hx':= budget_scale (show 0≤η⁻¹ by positivity) (hF x); refine budget_mono hx' ?_ ?_
  · intro i; split
    · exact mul_nonneg (h i|>.2.1) (Real.exp_pos _).le
    exact le_rfl
  intro z; dsimp only; rw [Beam.see,ht]; split
  next hh=>
    by_cases hs : U z ∧ w z
    swap; · unfold f; rw [if_neg hs,zero_mul]; exact hx'.1 z
    rw [if_pos (show x∈reachability (H:=H) z from hh ▸ (show (dashboard H z).site∈perf H z from Beam.see H z ▸ (Beam.dashboard H z).anchor)),if_pos hs.1,← (if_pos hs : f z=_)]
    change _ ≤ η⁻¹*(efface H Ω z*f z*Real.exp (a*coverNumber (radiusB s) (perf H z)))
    rw [← mul_assoc,← mul_assoc]; have hv' := (h z).2.1
    exact mul_le_mul (le_mul_of_one_le_left hv' ((one_le_inv_mul₀ hy).mpr (hx z hs.2))) (Real.exp_monotone (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))) (Real.exp_pos _).le (hv'.trans (le_mul_of_one_le_left hv' ((one_le_inv_mul₀ hy).mpr (hx z hs.2))))
  exact hx'.1 z

-- use threshold directly on comparison from solo heft (``shall`` read with immense)
lemma recognize {w:ℕ}{i} (h: ¬immense H w 3 (icon H i)) : coverNumber (radiusB s) (H.unionP (Brim.head i))≤ radiusB s := by
  have he : depth H (icon H i)<Pressure.Stores.till s := lt_of_not_ge (fun ht=> h (Or.inr (Or.inr ht)))
  have hv : depth H (icon H i)= H.shapeW (Brim.head i):= by simp [depth,icon,once]
  rw [hv] at he
  have hx: Ac.Spark H.supportP (Brim.head i):= by
    unfold Brim.head; refine ⟨singleton_nonempty _, fun i hi j hj=>?_⟩; rw [mem_singleton.mp hi,mem_singleton.mp hj]; exact .refl
  have hk:= ((shaped (H:=H) (Brim.head i) hx).trans he.le).trans (show (Pressure.Stores.till s:ℝ) ≤ radiusB s from by exact_mod_cast Nat.div_le_self ..)
  exact_mod_cast hk

def selectK (Δ:ℕ→Prop)(i:ℕ):ℝ:= if Δ i then 1 else 0
lemma kcop {i}{Δ:ℕ→Prop}:0 ≤ selectK Δ i:=by unfold selectK; split <;> norm_num

def Pics (Δ:ℕ→Prop) (p: BudgetPoint) (g:JointLoad.Heir.Record) (q κ χ:Chi) (e a k l:ℝ) := ∃ (b₁ b₂:ℕ→ℝ), (∀ i, p.Regular (plate H i).support (announced H g q κ e i) ∧ p.supBounds (plate H i).site (plate H i).support (announced H g q κ e i) (b₁ i)) ∧ Footprint.Anchored (fun i => (plate H i).site) (selectK Δ*b₁) (fun i => coverNumber p.B (plate H i).support) a k ∧ Footprint.Anchored (fun i=> (plate H i).site) (selectK Δ*b₂) (fun i=>coverNumber p.B (plate H i).support) a l ∧
        ∀ i, 0≤b₂ i ∧ p.Regular (plate H i).support (glyph H g q κ χ e i) ∧ (coverNumber p.B (plate H i).support ≤ p.B → p.supBounds (plate H i).site (plate H i).support (glyph H g q κ χ e i) (b₂ i))
lemma altar (Δ:ℕ→Prop)(g:JointLoad.Heir.Record)(q κ:Chi)(e a k l:ℝ)(t:ℕ)(he:preExponent p ≤ a)(ht:p.B=radiusB s)(h:Pics H Δ p g q κ χ e a k l) : Make H p χ (fun i=>¬immense H t 3 i ∧ solo H i Δ) (k+l):= by
  obtain ⟨f,u,hf,hy,hz,hu⟩:=h
  let w j:=f j+u j; let e':ℕ↪ H.fragrances:= ⟨icon H,icon_inj H⟩; let F z:= Function.extend e' w 0 z
  let P i:= ¬immense H t 3 i ∧ solo H i Δ; let v i:= if P i then F i else 0; let V:=dashboard H; let Φ i:= if P i then Song.sequence H (runway H) χ i else 0
  have h i : p.Regular (V i).support (Φ i) ∧ p.supBounds (V i).site (V i).support (Φ i) (v i) := by
    unfold v Φ V; split
    next h =>
      obtain ⟨hx,j,rfl,hj⟩:= h; rw [impact, show F (icon H j)=w j from (e'.injective.extend_apply w (0:H.fragrances→ℝ) j),show Song.sequence H (runway H) χ (icon H j)=announced H g q κ e j-glyph H g q κ χ e j from (by ext x; rw [Song.sequence, stale]; change (-1:ℝ)*_=_- (stream H χ x (icon H j)+_); ring)]
      have he:=recognize H hx; rw [← ht,concern H] at he
      exact ⟨CouplingShape.reg_sub (hf j).1 (hu j).2.1, CouplingShape.sup_sub (hf j).1 (hu j).2.1 (hf j).2 ((hu j).2.2 he)⟩
    exact ⟨CouplingShape.reg_const _, VerifiedReset.sup_le (CouplingShape.sup_const _) (le_of_eq abs_zero)⟩
  refine ⟨v,fun x=> ?_,fun i=> by by_cases he: P i <;> simpa only [V,Φ, if_pos, if_neg, he, show (fun i=>¬immense H t 3 i∧solo H i Δ) i=P i from rfl] using h i⟩; let X z:=if (V z).site=x then v z*Real.exp (preExponent p*coverNumber p.B (V z).support) else 0
  change SumBudget X (k+l); have hx i:0≤X i:= by unfold X; split; exact mul_nonneg (h i|>.2.1) (Real.exp_pos _).le; exact le_rfl
  apply wallet e'; refine budget_mono (budget_plus (hy x) (hz x)) (fun i=> hx _) ?_
  · intro i; unfold X; rw [show V (e' i)=plate H i from impact ..]; split
    next hh=>
      by_cases hs:P (e' i)
      · obtain ⟨hZ,j,hj,hJ⟩:= hs; have hi: i=j:= icon_inj H hj; subst j
        have hf' : selectK Δ i=1:= if_pos hJ
        dsimp only
        apply (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))) (h (e' i)|>.2.1)).trans_eq
        unfold v F w; rw [if_pos ⟨hZ,_,hj,hJ⟩,e'.injective.extend_apply]; simp only [Pi.mul_apply,hf',one_mul,add_mul]
      rw [show v (e' i)=0 from if_neg hs,zero_mul]; simpa only [if_pos hh] using (budget_plus (hy x) (hz x)).1 i
    next h=> norm_num
  intro i hi; unfold X v; split
  · rw [if_neg (show ¬P i from (fun h=> hi (by obtain ⟨j,hj,-⟩:= h.2; exact ⟨j,hj.symm⟩))),zero_mul]
  rfl

-- plenty high + proportional stint on mixed part; exact description at immersion threshold & outstanding Solo cost.
lemma tall (p':H.fragrances→Prop) (Δ:ℕ→Prop) (K:ℕ) (N:Captain H j C' d v Y A b r B q k χ) (hr:p.threshold=Pressure.temp s)(hB:p.B=radiusB s)(ht:preExponent p≤ a)(hw:p.order≤j)(hf:p.power ≤ n) (u l:ℝ) (Ω:ℕ→ℝ) (η:ℝ) (hg:0<η)(hu:∀ i,1≤Ω i)(hh:∀ i,Δ i → η≤Ω i)
    (hs: Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z=>if immense H K K z then efface H Ω z*N.markΦ z n else 0) a u)
    (hs': Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z=>if immense H K 3 z then efface H Ω z*N.markΦ z n else 0) a l)
    (D:JointLoad.Heir.Record)(κ q':Chi)(γ:ℝ)(ha:preExponent p ≤ γ) (α' δ₀ δ₁:ℝ) (hQ:Pics H Δ p D q' κ χ α' γ δ₀ δ₁)
    (hF:∀ i, p' i → ¬Terrain.Lantern H K Δ i) : Make H p χ p' ((1:ℝ)⁻¹*u+(η⁻¹*l+(δ₀+δ₁))):= by
  have hm:= frost H p χ _ N hr hB ht hw hf 1 u (fun _=>True) (fun i _=>one_le_prod (s:=univ) (f:=fun k=> feel Ω (S:=S) (i.2 k).val) (fun k _=> feel_pos hu _)) zero_lt_one hs
  have hx:= frost H p χ _ N hr hB ht hw hf η l (latent H Δ) (paidit H hu hh) hg hs'; have hY:= altar H p χ Δ D q' κ α' γ δ₀ δ₁ K ha hB hQ
  refine nextK H p χ _ _ (shed H p χ _ _ hm (shed H p χ _ _ hx hY)) ?_
  intro z hz x hx
  by_cases he:immense H K K z; · exact Or.inl ⟨he,trivial⟩
  have hv : latent H Δ z:= by_contra fun h=> hF z hz (sprite H K hx h he)
  apply Or.inr; by_cases hp:immense H K 3 z; · exact Or.inl ⟨hp,hv⟩
  exact Or.inr ⟨hp, senate H K hx hv hp⟩
end YM.PhysicalNext.Repeat.Terrain
