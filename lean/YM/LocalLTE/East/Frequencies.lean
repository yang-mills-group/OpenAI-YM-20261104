import YM.LocalLTE.Fan.Local
import YM.LocalLTE.Tile.Allot
import YM.LocalLTE.Tier.Dais
/-! # Sharp itinerary frequency
All labels common, support ball of E_q leaves specified only at epochs whose radius G design. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.East
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Height LocalLTE.Fan Pastel -- namespace edit
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {T₀ : Patch} {ℓ k j n: ℕ} {K : Teller G} {s a W U V g C' y A M K₀ r β δ q b v σ t w Λ γ: ℝ} {m : ℕ}
variable {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} (H : Cash W s a L X o U T R) {I: Cash W s a L X o U T R'} {χ : Chi}
local notation "B" => radiusB s
abbrev EBill (c f:Side) := Veil c f
abbrev DiskShelf (p:ℕ) (c f:Side) := Option (Fin p) → Finset (EBill c f)
def lining (S:StepData c f) (p:Molecule S) : Finset (EBill c f):= p.preimage (LocalLTE.Fan.elastic) (LocalLTE.Fan.runOut (S:=S)).injOn
def docket (z:H.fragrances): DiskShelf z.fst c f:=fun i=> East.lining S (z.2 i).val
def traceO (S : StepData c f) (R:Rep G f): EBill c f→ Site c:= Sum.elim (fun i=> S.ratio.parent (R.activities.reg i).site) (Mint.pace S)
-- contraction input model Z≤(radiusB s)*L. Output choice ℒ tape radius before L.
def spacious (v:Finset (EBill c f))(n:ℕ):Prop:= ∀ (i:ℕ),Sum.inl i∈ v→(R.activities.reg i).support⊆ neighbors n (R.activities.reg i).site -- edit unused H R
structure Credits (p:H.ThinP) (v:Finset (EBill c f)) (ℓ:ℕ) : Prop where
  burns : Ac.Spark H.supportP p.val
  players : troupe T R X.halo B p.val
  lift : p.val=LocalLTE.Fan.arm v
  received : v.card ≤ ℓ
  stretch (k:Mint.Music c f) : Sum.inr k∈v → Mint.verse R.path k ≤ B
  track : East.spacious (R:=R) v (S.patch.L.val*B)
structure Orchestra (z:H.fragrances) (ℓ:ℕ):Prop where
    length : z.fst ≤ ℓ
    each i : Credits H (z.2 i) (East.docket H z i) ℓ
    ancestor : Height.ancestry z
    nonempty : coefficient H.seam z.2≠0

lemma arises (u:H.fragrances) (hx: ¬Height.tiredN H ℓ u) (V: Config G c)(hv:stream H χ V u ≠ 0) (he: Height.ancestry u) (hp : ∀ i, East.spacious (R:=R) (East.docket H u i) (S.patch.L.val*B)): Orchestra H u ℓ:=by
   obtain ⟨h,hu⟩:= aging hv hx
   refine ⟨hu.le,fun i=>?_,he,fun h=>hv (by unfold stream Gas.term; rw [h,zero_mul,zero_div])⟩
   have hi := h i; let p:=u.2 i
   let k:= elastic (S:=S); let Z:= East.lining S p.val
   have hz (j:EBill c f): j∈ Z ↔ k j∈ p.val:= Finset.mem_preimage
   have hh w (hf:w∈p.val): w∈Set.range k := by
     rcases w with w|w
     · have hL:= mem_toLeft.mpr hf; rw [hi.unforced] at hL; exact (notMem_empty _ hL).elim
     have he' : Silica.hornN ℓ w < ℓ := by
        have h:Silica.hornN ℓ w ≤ acmeN H ℓ u:= le_trans (b:=pinsN ℓ S p.val) (single_le_sum (f:=Sum.elim _ _) (fun _ _=>Nat.zero_le _) hf) (single_le_sum (f:=fun j=> pinsN ℓ S (u.2 j).val) (fun _ _=> Nat.zero_le _) (mem_univ i))
        have hv:= lt_of_not_ge (not_or.mp hx).1; unfold degreeN at hv; omega
     rcases w with w|w|w
     · have hv: w∈ own (u.2 i).val:= mem_toLeft.mpr (mem_toRight.mpr hf); rw [hi.noK] at hv; exact (notMem_empty _ hv).elim
     · rcases w with w|w|w
       · rcases w with w|w|w|w|w|w -- Music 3
         · exact ⟨.inl w,rfl⟩
         · exact ⟨.inr (.inl w),rfl⟩
         · exact ⟨.inr (.inr (.inl w)),rfl⟩
         · exact ⟨.inr (.inr (.inr (.inl w))),rfl⟩
         all_goals exfalso; change ℓ+2<ℓ at he'; omega
       · exact ⟨.inr (.inr (.inr (.inr w))),rfl⟩
       exfalso; change ℓ+2<ℓ at he'; omega
     exfalso; change ℓ+2<ℓ at he'; omega
   have hZ:p.val=Z.image k:=by
      ext v; constructor; · intro hy; obtain ⟨r,rfl⟩:=hh _ hy; exact mem_image_of_mem k ((hz _).2 hy)
      intro hy; obtain ⟨r,he,rfl⟩:=mem_image.mp hy; exact (hz _).1 he
   have hL: leaflet H χ V p≠0 :=fun h=>hv (by unfold stream Gas.term; rw [prod_eq_zero (mem_univ i) h,mul_zero,zero_div]); have hV': troupe T R X.halo (radiusB s) p.val :=by
       by_contra hx; apply hL; unfold March.leaflet likely; simp_rw [vacuity V p (fun h=> hx h.2),sum_const_zero,mul_zero] -- edit
   have ht: (Z).card≤ ℓ:= by rw [← Finset.card_image_of_injective Z (show Injective k from runOut), ←hZ]; exact hi.few
   refine ⟨hi.connects,hV',hZ,ht,?_, hp i⟩
   intro i' hi'; have hL:= (hz (.inr i')).1 hi'
   refine (Nat.cast_le (α:=ℝ)).mp (le_trans ?_ hi.pays)
   change _ ≤ Finset.sum _ _; apply le_trans _ (Finset.single_le_sum (fun v hv=> ?_) hL)
   swap;
   · obtain ⟨w,hw⟩:= hh v hv; subst v; exact add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
   rw [balance T R i']; have ht: note i'=chapter (.inr i'):= by rcases i' with i'|i'|i'|i' <;>rfl
   rw [ht]; exact le_add_of_nonneg_left (Nat.cast_nonneg _)
end YM.PhysicalNext.Repeat.East
