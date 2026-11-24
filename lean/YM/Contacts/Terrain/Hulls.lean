import YM.Contacts.Terrain.Magnet
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Beam.Young
/-! Who can be left after pricing immense plus outstanding legacy (E) hits.
 Doesn't pay logarithms/tails yet. A survival certificate is effective ONLY in
 the full Cash family and primary arrays BEFORE dividing by conditional density.
 Earned by real Brush & universal capture events; no Laplace formal input here. -/
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

lemma willing (z : H.fragrances) (V : Config G c) (h : stream H χ V z≠0) (k : Option (Fin z.1)) :
    Ac.Spark H.supportP (z.2 k).val ∧ troupe T R Q.halo (radiusB s) (z.2 k).val := by
  contrapose! h with he
  have hx : ¬(Ac.Spark H.supportP (z.2 k).val ∧ troupe T R Q.halo (radiusB s) (z.2 k).val):= fun H=> he H.1 H.2
  have hh : leaflet H χ V (z.2 k)=0:= by unfold leaflet likely; simp_rw [vacuity V _ hx,sum_const_zero,mul_zero]
  unfold stream Gas.term; rw [prod_eq_zero (Finset.mem_univ k) hh,mul_zero,zero_div]

/-- removes only (resp. seed, K) by overlap; no bound on shares. -/
lemma arctic (p : H.ThinP) (hp : troupe T R Q.halo (radiusB s) p.val) (hu : Cash.numP p.val < 1) : p.val.toLeft=∅∧own p.val=∅ := by
  have he : p.val.toLeft= ∅ := Finset.not_nonempty_iff_eq_empty.mp fun ⟨i,hi⟩=> by
    have hx : 1 ≤ i.shares:= by rw [← Packets.seeds_card]; exact Finset.card_pos.mpr (hp.1.checkpoints i hi).1
    exact (Nat.not_lt.mpr (hx.trans (show i.shares≤Cash.numP p.val from Finset.single_le_sum (f:=Mixed.shares S) (fun _ _=> Nat.zero_le _) (mem_toLeft.mp hi)))) hu
  refine ⟨he,Finset.not_nonempty_iff_eq_empty.mp ?_⟩
  rintro ⟨i,hi⟩; obtain ⟨j,hj⟩ := (R.activities.forced i).inventory_ne; obtain ⟨z,hy,hv⟩:=hp.2.2 _ hi _ hj
  unfold roster Packets.store at hy; rw [he] at hy; simp at hy

def latent (Δ:ℕ→Prop) (z:H.fragrances) := ∃ k : Option (Fin z.1), ∃ i:ℕ, Δ i ∧ Opacity.key S i∈ (z.2 k).val
variable (w:ℕ)
lemma acausal (z:H.fragrances) {k} {i:ℕ} (hi:Opacity.key S i∈(z.2 k).val) : 1 ≤ extraTag H w z := by
  apply le_trans (single_le_sum (f:=fun p=> Sum.elim (fun _=>0) (modern w (c:=c) (f:=f)) p) (fun i _=> Nat.zero_le _) hi)
  exact single_le_sum (f:= fun k=> sprawls w S (z.2 k).val) (fun i _=>Nat.zero_le _) (mem_univ k)

def solo (z:H.fragrances) (Δ:ℕ→Prop) := ∃ i:ℕ,z=icon H i ∧ Δ i
lemma senate {z:H.fragrances} {V:Config G c} (h:stream H χ V z≠0) {Δ} (hp:latent H Δ z) (hh: ¬immense H w 3 z) : solo H z Δ := by
  obtain ⟨k,i,hi,hx⟩:= hp; refine ⟨i,Beam.lantern z (fun i=> Finset.card_pos.mpr (willing H z V h i).1.1) ?_ k hx,hi⟩
  have he: extraTag H w z+breadth H z<3:= lt_of_not_ge (not_or.mp hh).1; have hv:= acausal H w z hx; omega

private lemma pillarA {A: Type*} {s:Finset A} {f:A→ℝ} (hf: ∀ i∈s,1≤f i) {a:A} (ht:a∈s): f a≤∏ i∈s,f i:= by
  conv_rhs => rw [← mul_prod_erase _ _ ht]
  exact le_mul_of_one_le_right (zero_le_one.trans (hf a ht)) (one_le_prod (fun i hi=> hf i (mem_of_mem_erase hi)))
lemma paidit {Δ} {Ω:ℕ→ℝ} (hΩ:∀ i,1≤Ω i) (ht:∀ i,Δ i → d≤Ω i) (z:H.fragrances) (hp:latent H Δ z) : d≤efface H Ω z := by
  obtain ⟨k,i,hx,hi⟩:=hp; refine (ht i hx).trans ((pillarA (f:= hairs (S:=S) Ω) (fun i _=> hairs_pos (S:=S) hΩ _) hi).trans (pillarA (f:=fun k=> feel (S:=S) Ω (z.2 k).val) (fun i _=> feel_pos hΩ _) (mem_univ k)))

/-- Coordinates only; actual cluster reachability recovered from h.participation. -/
structure Lantern (Δ:ℕ→Prop) (z:H.fragrances) : Prop where
  hiatus : depth H z <Pressure.Stores.till s
  members : extraTag H w z+breadth H z<w
  participation : coefficient H.seam z.2≠0
  travels (i: Option (Fin z.1)): Ac.Spark H.supportP (z.2 i).val ∧ troupe T R Q.halo (radiusB s) (z.2 i).val
  heart (i : Option (Fin z.1)) (x : Head S) (hp:x∈(z.2 i).val): Pennies S x ∨ ∃ k:ℕ, ¬Δ k ∧ x=Opacity.key S k
lemma sprite {Δ}{z:H.fragrances} {V:Config G c} (h:stream H χ V z≠0) (hp:¬latent H Δ z) (hq:¬immense H w w z) : Lantern H w Δ z := by
  have ht := lt_of_not_ge (not_or.mp hq).1
  have hx := willing H z V h
  refine ⟨lt_of_not_ge (not_or.mp (not_or.mp hq).2).2,ht,fun h'=> h (by unfold stream Gas.term; rw [h',zero_mul,zero_div]),hx,?_⟩
  intro i x hi; obtain ⟨hy,hF⟩:= arctic H _ (hx i).2 (lt_of_le_of_lt (single_le_sum (s:=univ) (f:=fun k=> Cash.numP (z.2 k).val) (fun i _=>Nat.zero_le _) (mem_univ i)) (show overlap H z < 1 from lt_of_not_ge (not_or.mp (not_or.mp hq).2).1))
  rcases x with x|x
  · exact False.elim (by have h:= mem_toLeft.mpr hi; rw [hy] at h; exact notMem_empty _ h)
  have he: modern w x < w:= by
    apply lt_of_le_of_lt ?_ ht
    refine le_trans (b:=sprawls w S _) (single_le_sum (f:=Sum.elim _ _) (s:=(z.2 i).val) (fun i _=> Nat.zero_le _) hi) ?_
    apply (single_le_sum (s:=univ) (f:=fun k=> sprawls w S (z.2 k).val) (fun i _=>Nat.zero_le _) (mem_univ i)).trans
    exact Nat.le_add_right ..
  rcases x with x|x|x
  · exact False.elim (by have h : x∈ own (z.2 i).val:= mem_toLeft.mpr (mem_toRight.mpr hi); rw [hF] at h; exact notMem_empty _ h)
  · rcases x with x|x|x
    · rcases x with x|x|x|x|x|x
      · exact Or.inr ⟨x,fun h=> hp ⟨i,x,h,hi⟩,rfl⟩
      · exact Or.inl ⟨_,rfl, trivial⟩
      · exact Or.inl ⟨_,rfl, trivial⟩
      · exact Or.inl ⟨_,rfl, trivial⟩
      all_goals exact (Nat.lt_irrefl _ he).elim
    · exact Or.inl ⟨_,rfl,trivial⟩
    exact (Nat.lt_irrefl _ he).elim
  exact (Nat.lt_irrefl _ he).elim
end YM.PhysicalNext.Repeat.Terrain
