import YM.Juniper.Bright.Victor
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Reframe
/-!
 # Classification of actual high-order graph contribution

 Low-cost can include **non-isolated** E inherits; must use with their
 support norms to continue decomposition. For pure reception this vanishes
 pointwise on the FULL kernel and repairs all slots. Colon:'force' not just
 just outside the cuts. Genuine re-expression sparsity: all selectors
 compared in exact Hop unmasked function at all U. This is where we use
 weighted and period conditions, not any duplicate-R argument. Adaptation
 of Beam.kids from `Census.Wing`.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Bright
open ConnectedActivityE6 Blaze Silica March Captain PhysicalNext PhysicalNext.Repeat Height
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Shoot SliceRows Control Pulse Mask Raw Matter Pond Gas Ursell Trees Reserves Greenbelt Deck Mint Shield Stained
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Extra.Iteration
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G: Gauge} {c f L : Side} {P:Teller G} {S: StepData c f} {T: Tube G S} {R : Rep G f}
      {W μ x C s:ℝ} {χ:Chi}{Q: ConnectedActivityE6.Target G P} {o:Target.Order G W} {I:Cash W x μ L Q o C T R}
      {j n:ℕ} {V : Config G c}
local notation "η" => radiusB x
local notation "ζ" => Pressure.Stores.till x
local notation "Λ" => L.val
section
-- presence of a nonzero leaf implies every factor received, uniformly under its internal tag choices. Doesn't assert independent witnesses for joint occupancy.
variable (I :Cash W x μ L Q o C T R) (z:I.fragrances) (hZ:stream I χ V z ≠0)
include hZ
lemma earns (i) : leaflet I χ V (z.2 i) ≠0 := fun h=> hZ (by unfold stream Gas.term; rw [prod_eq_zero (mem_univ i) h,mul_zero,zero_div])
lemma profitable : coefficient I.seam z.2 ≠0 := fun h=> hZ (by unfold stream Gas.term; rw [h,zero_mul,zero_div])
lemma merit (i) : Ac.Spark I.supportP (z.2 i).val ∧ troupe T R Q.halo η (z.2 i).val := by
  by_contra h; apply earns I z hZ i; unfold leaflet Pond.likely
  simp_rw [vacuity V (z.2 i) h,sum_const_zero,mul_zero]
lemma earned (i) {u :Head S} (hu:u∈(z.2 i).val) : ¬(∀ (F:Forest S.ratio) (X:Coat T F),X.x=x→ ∀ A k, Polar.ember X o.a R W Q.table (Vine.worldZ X R.beta A) (X.input (Vine.worldZ X R.beta A)) A k Q.halo u=0):= by
   intro h; apply earns I z hZ i; unfold leaflet Pond.likely Stained.fringe
   let p:= (z.2 i).val
   have hx (F:Forest S.ratio) (X:Coat T F) (ht:X.x=x) (d) (k) : Polar.floating X o.a R W Q.table d k Q.halo p=0 := Finset.prod_eq_zero hu (h F X ht d k)
   have he (F:Forest S.ratio) (X:Coat T F)(ht:X.x=x) : Shield.shelter X W o.a p R Q.table Q.halo=0 := by
       have hh i d k b:Polar.floating (((preps X (roster p)).taggedL i).wrapY d) o.a R W Q.table k b Q.halo p=0:= hx F (((preps X (roster p)).taggedL i).wrapY d) ht _ _
       unfold Shield.shelter; split; next=> unfold Shield.seating; dsimp only; unfold Shield.bars; simp only [hh,mul_zero,integral_zero,sum_const_zero,Pond.likely]
       rfl
   have hk (F:Tree.Forest S.ratio) k: Shield.shelter ((Greenbelt.prism T x χ o.K V F).rinse k) W o.a p R Q.table Q.halo=0:= he F _ (show ((Greenbelt.prism T x χ o.K V F).rinse k).x=_ from rfl)
   change _ * ∑ i: Greenbelt.Reserve S, (∫ z, Shield.shelter _ _ _ p R Q.table Q.halo ∂ _)=_; simp only [hk,integral_zero,sum_const_zero,mul_zero]
variable (h : ¬ high I n z)
include h
omit hZ in
lemma from_head (i) {u :Head S}(hu : u∈ (z.2 i).val) : boltKey S (welfare n c f) u < n:= by
   apply lt_of_le_of_lt _ (lt_of_not_ge (fun hp=> h (Or.inl hp))) -- proof
   exact ((single_le_sum (f:=boltKey S (welfare n c f)) (fun _ _=> Nat.zero_le _) hu).trans ((single_le_sum (f:=fun i=>bill S (boltKey S (welfare n c f)) (z.2 i).val) (fun _ _=>Nat.zero_le _) (mem_univ i)).trans (Nat.le_add_left ..)))
omit hZ in
lemma bounded_debt (i) {u: Alphabet c f} (hu: Sum.inr u∈ (z.2 i).val): lengths T R u < ζ / (Λ:ℝ):= by
  let p:= (z.2 i).val; let a:= Mixed.lengths S I.faresP (lengths T R); let f u:= weight I.supportP η a u
  have hh (i):0≤a i:= by
    rcases i with i|i
    · exact mul_nonneg I.laws.acquired.extra (Nat.cast_nonneg _)
    exact Nat.cast_nonneg _
  exact ((show lengths T R u ≤ f (.inr u) from le_add_of_nonneg_left (Nat.cast_nonneg _)).trans_lt
   (lt_of_le_of_lt (b:=I.shapeW p) (Finset.single_le_sum (f:=f) (fun i _=> add_nonneg (Nat.cast_nonneg _) (hh i)) hu) ((lt_of_le_of_lt (b:= Height.depth I z) (single_le_sum (f:=fun i=> I.shapeW (z.2 i).val) (fun i _=> I.positive_volume _) (mem_univ i)) (lt_of_not_ge (fun hp=> h (Or.inr (Or.inr hp))))))))
omit h hZ in
private lemma logs_small {Y: PathData G} {c:Side} (p:Raw.Pairs c) {d : ℕ} (hd:d ≤ L.val) (ht: (Raw.bothCharge Y p:ℝ)<ζ/(Λ:ℝ)) : ¬ Raw.long Y ζ d p.2.1 p.2.2.2 := by -- namespace long
   have he:bothCharge Y p*L.val ≤ ζ:= by exact_mod_cast ((lt_div_iff₀ (by positivity)).mp ht).le
   unfold bothCharge at he; rw [Paths.duplex_price] at he
   -- tactic syntax `not_long` on Nat
   unfold Raw.long; rw [not_not]; constructor<;>nlinarith
lemma material_head (i) {u :Head S}(hu:u∈(z.2 i).val): (∃ j, Opacity.key S j=u ∧ ∃ p, R.activities.regularOccurrence R.p j p≠0) ∨ ∃ j, Mint.disc S j=u∧ Mint.verse R.path j≤ η:= by
   let p:= (z.2 i).val
   have hz:= earns I z hZ i; have hh:= earned I z hZ i hu; have ha:= from_head I z h i hu; obtain ⟨hv,hU⟩:= merit I z hZ i
   have hpj (p: Coat.LogIndex c f)(h:(.inr (.inr (.inl p)):Head S) ∈(z.2 i).val) : (Coat.exCharge T R p:ℝ)< ζ /(Λ:ℝ):= bounded_debt I z ‹¬_› i h
   have hy: S.patch.L=L:= I.laws.data.funds.length_eq -- edit
   have hk : 0<Λ:= L.property
   have ht:Pressure.Stores.till x≤ η := Nat.div_le_self ..
   have hQ : ∀ y:ℕ,(y:ℝ)<ζ/(Λ:ℝ) → y≤ η :=by
     intro y hy; have hx: (y:ℝ) * Λ ≤ Pressure.Stores.till x:= ((lt_div_iff₀ (by exact_mod_cast hk)).mp hy).le
     exact le_trans ((Nat.le_mul_of_pos_right _ hk).trans (by exact_mod_cast hx)) ht
   have hu' : p.toLeft=∅:= Finset.not_nonempty_iff_eq_empty.mp (by
      rintro ⟨d,hd⟩; apply h; have hx: 1≤d.shares:=by rw [← Packets.seeds_card]; exact Finset.card_pos.mpr (hU.1.checkpoints d hd).1
      have hX : d.shares≤Cash.numP p := Finset.single_le_sum (f:= Mixed.shares S) (fun i _=> Nat.zero_le _) (mem_toLeft.mp hd)
      exact Or.inr (Or.inl ((hx.trans hX).trans (single_le_sum (f:= fun i=> Cash.numP (z.2 i).val) (fun i _=>Nat.zero_le _) (mem_univ i)))))
   rcases u with u|u|u
   · exact absurd (show p.toLeft.Nonempty from ⟨u,mem_toLeft.mpr hu⟩) (by simp [hu'])
   -- K MUST require some seed!
   · obtain ⟨y,he⟩:= (R.activities.forced u).inventory_ne; obtain ⟨k,hk,hK'⟩:= hU.2.2 u (mem_toLeft.mpr (mem_toRight.mpr hu)) y he; exfalso
     unfold roster Packets.store at hk; rw [hu'] at hk; simp at hk
   rcases u with u|u
   swap; · exact (lt_irrefl n ha).elim -- ha defeq
   have hB:= hpj u hu
   rcases u with u|u|u
   swap; · exact Or.inr ⟨.inr (.inr (.inr u)),rfl,Nat.zero_le _⟩
   swap; · exact (lt_irrefl n ha).elim
   rcases u with u|u|u|u|u|u
   · refine Or.inl ⟨u,rfl,?_⟩
     by_contra! H; apply hh; intro p V _ d k
     change Real.exp (-(R.activities.regularOccurrence R.p u _) * _) -1= 0; rw [H,neg_zero,zero_mul,Real.exp_zero,sub_self]
   · exact Or.inr ⟨.inl u,rfl,hQ _ hB⟩
   · exact Or.inr ⟨.inr (.inl u),rfl,hQ _ hB⟩
   · exact Or.inr ⟨.inr (.inr (.inl u)),rfl,hQ _ hB⟩
   · exfalso; apply hh; intro F X ht A b
     have hv:= logs_small (L:=L) u hk (Y:=R.path) (x:=x) hB
     change Real.exp (pairValue R.path R.clip _ (till X.x) 1 _ _ u * _) -1=0
     rw [ht]; unfold pairValue Raw.pairTail; simp only [hv,false_and, ↓reduceIte, mul_zero,zero_mul,Real.exp_zero,sub_self]
   exfalso; apply hh; intro F X hT A b;
   have hv:= logs_small (L:=L) u (by rw [hy] : S.patch.L.val ≤ Λ) (Y:=T.down) (x:=x) hB -- hy.le on Side→Nat
   change Real.exp (Polar.icicle T.down _ (till X.x) S.patch.L.val _ u * _) -1=0; rw [hT]; unfold Polar.icicle Polar.twin; simp only [hv,↓reduceIte,mul_zero,zero_mul,Real.exp_zero,sub_self]
end
end YM.Juniper.Bright
