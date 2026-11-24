import YM.LocalLTE.East.Frequencies
import YM.LocalLTE.E6.Dossier
/-! Beyond arbitrary LTE letter count, true survivors; no inherited calls in the universal Kin sector. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Height
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration Brim Greenbelt
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i : ℝ} {k j n ℓ : ℕ} {F : Tree.Forest S.ratio}
    {χ : Chi} {H : Cash W s μ L Q o α T R}

lemma aged {z:H.fragrances}(hv:∀ i,Ac.Spark H.supportP (z.2 i).val∧ troupe T R Q.halo (radiusB s) (z.2 i).val) (he : ¬tiredN H ℓ z):
    (∀ i,Elder ℓ (z.2 i)) ∧ z.1< ℓ:= by
  obtain ⟨hp,hr,hd⟩:= (and_congr Iff.rfl not_or|>.1 (not_or.mp he))
  have ht := lt_of_not_ge hp
  have he : breadth H z < ℓ := lt_of_le_of_lt (Nat.le_add_left ..) ht
  constructor
  · intro i; let k: H.ThinP:=z.2 i
    obtain ⟨hs,hh⟩:= hv i
    have hu : Cash.numP k.val <1:= lt_of_le_of_lt (single_le_sum (s:=univ) (f:=fun j=> Cash.numP (z.2 j).val) (fun _ _=> Nat.zero_le _) (mem_univ i)) (lt_of_not_ge hr)
    have hF:k.val.toLeft=∅ := Finset.not_nonempty_iff_eq_empty.mp fun ⟨w,hw⟩=> by
      have hx : 1 ≤ w.shares:= by rw [← Packets.seeds_card]; exact Finset.card_pos.mpr (hh.1.checkpoints w hw).1
      exact (Nat.not_lt.mpr (hx.trans (show w.shares≤Cash.numP k.val from Finset.single_le_sum (f:=Mixed.shares S) (fun _ _=> Nat.zero_le _) (mem_toLeft.mp hw)))) hu
    refine ⟨hs,hF,Finset.not_nonempty_iff_eq_empty.mp ?_,Finset.card_pos.mpr hs.1,(single_le_sum (f:=fun j=> (z.2 j).val.card) (fun _ _=>Nat.zero_le _) (mem_univ i)).trans he.le,?_⟩
    · rintro ⟨t,ht⟩; obtain ⟨j,hj⟩ := (R.activities.forced t).inventory_ne; obtain ⟨l,hy,hv'⟩:=hh.2.2 _ ht _ hj
      unfold roster Packets.store at hy; change (z.2 i).val.toLeft= _ at hF; rw [hF] at hy; simp at hy
    exact le_trans (single_le_sum (f:=fun i=>H.shapeW (z.2 i).val) (fun i _=> H.positive_volume _) (mem_univ i)) ((lt_of_not_ge hd).le.trans (by exact_mod_cast Nat.div_le_self ..))
  exact lt_of_lt_of_le (Nat.lt_succ_self z.1) ((Beam.on_one z (fun i=>Finset.card_pos.mpr (hv i|>.1.1))).trans he.le)

end YM.PhysicalNext.Repeat.Height
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
lemma arisesQ (u:H.fragrances) (hx: ¬Height.tiredN H ℓ u) (hq: coefficient H.seam u.2≠0)(hv:∀ i,Ac.Spark H.supportP (u.2 i).val∧ troupe T R X.halo (radiusB s) (u.2 i).val) (he: Height.ancestry u) (hp : ∀ i, East.spacious (R:=R) (East.docket H u i) (S.patch.L.val*B)): Orchestra H u ℓ:=by
   obtain ⟨h,hu⟩:= aged hv hx
   refine ⟨hu.le,fun i=>?_,he,hq⟩
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
   have hV':troupe T R X.halo (radiusB s) p.val:=(hv _).2
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
