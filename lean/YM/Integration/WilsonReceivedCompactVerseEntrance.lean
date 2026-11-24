import YM.Integration.WilsonReceivedMicroscopicVerseWallet

/-! The independent exporter may post a compact group program that retains every previously
deposited connected word, before the finite Wilson update. Its native finite chart is folded. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCompactVerseEntrance
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Tree Exterior Stationary
open PowerSeries Next.Free FormalBulk08 Flat Reef Jets Series Shore Gorge Lotus Mesa City Cork
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Cosmos WilsonPointChildPlacedFamily
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open PhysicalNext.Repeat.Legato Next.Foundations Pose Dawn Kemp Rift
open WilsonMarkedIndependentPhysicalIntake WilsonPointChildFiledPress
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Realm
open WilsonOlderFreshConnectedRobe
open scoped Classical BigOperators


open WilsonReceivedDatedVerseReprint
open WilsonReceivedMicroscopicVerseWallet (gross tariff one buys)
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{h k:I → ℕ}{e:ℕ}

def submit (Y:Outerm G h)(k:I → ℕ)(e:ℕ):Outerm G h:=fun y J=>
  if v:J.Nonempty then printed Y k e J v.choose y else 0

def CoverBill (Y:Outerm G h)(e:ℕ)(s A:ℝ):Prop:=
  ∀y J a,a ≤ e → ∀r,Wig Bank.terrain y s (A^J.card) J ((Y y J).2 a r)

omit [DecidableEq I] in
theorem word (Y:Outerm G h)(well:Wellness k Y){s A:ℝ}(hs:0<s)(pos:0 ≤ A)
    (cover:CoverBill Y e s A)(J:Finset I):
    ∃t C:ℝ,0<t ∧ t ≤ s ∧ 0 ≤ C ∧ ∀(c:I),c∈J → ∀y,
      Issued Y k e J c y t s C (A^J.card) ∧ Auth (mass k J) (printed Y k e J c y):=by
  obtain ⟨t,C,hT,bound,hC,ready⟩:=planet G J.card (mass k J) (e+1) s hs
  refine ⟨t,C,hT,bound,hC,?_⟩
  intro c root y
  obtain ⟨rain,rent,jet⟩:=ready _ (Y y J) I J y c _ (well.level' y J) root le_rfl (pow_nonneg pos _)
    (fun a ha r=>cover y J a (Nat.le_of_lt_succ ha) r) (e+1) le_rfl
  exact ⟨⟨rain,rent,fun a ha=>shineZ (Y y J) y rain hT jet a (Nat.lt_succ_of_le ha)⟩,
    (root_robe _ rain hT (y c)).1⟩

omit [DecidableEq I] in
theorem original (Y:Outerm G h)(well:Wellness k Y){s A:ℝ}(hs:0<s)(hA:1 ≤ A)
    (cover:CoverBill Y e s A):
    let posted:=submit Y k e
    let B:=gross G (mass k univ+e) s 1*A
    1 ≤ B ∧ Wellness k posted ∧
    (∀y J a,a ≤ e → (posted y J).2 a=(Y y J).2 a ∧ ∀n r,
      (posted y J).1 n a r=plume ((Y y J).2 a r) n) ∧
    ∀n,PairedAt e posted n (s/32) B:=by
  classical
  intro posted B
  have positive:0 ≤ A:=zero_le_one.trans hA
  have hB:1 ≤ B:=one_le_mul_of_one_le_of_one_le (one ..) hA
  have earned (J:Finset I)(c:I)(root:c∈J)(y:I → Cover):
      Auth (mass k J) (printed Y k e J c y) ∧
      ∀a ≤ e,(printed Y k e J c y).2 a=(Y y J).2 a ∧ ∀n r,(printed Y k e J c y).1 n a r=plume ((Y y J).2 a r) n:=by
    obtain ⟨t,C,_,_,_,paid⟩:=word Y well hs positive cover J
    exact ⟨(paid c root y).2,(paid c root y).1.2.2⟩
  have legal:Wellness k posted:=by
    refine ⟨fun y=>by simp [posted,submit],?_,?_⟩
    · intro y J
      by_cases hj:J.Nonempty
      · simpa only [posted,submit,dif_pos hj] using (earned J hj.choose hj.choose_spec y).1
      · have empty:J=∅:=Finset.not_nonempty_iff_eq_empty.mp hj
        subst J
        rw [show posted y ∅=0 from by simp [posted,submit]]
        simpa only [well.quiet' y] using (well.level' y ∅)
    · intro y z J same
      by_cases hj:J.Nonempty
      · simp only [posted,submit,dif_pos hj,printed,sphere,well.filial y z J same,same _ hj.choose_spec]
      · simp [posted,submit,hj]
  have files (y:I → Cover)(J:Finset I)(a:ℕ)(ha:a ≤ e):
      (posted y J).2 a=(Y y J).2 a ∧ ∀n r,(posted y J).1 n a r=plume ((Y y J).2 a r) n:=by
    by_cases hj:J.Nonempty
    · simpa only [posted,submit,dif_pos hj] using (earned J hj.choose hj.choose_spec y).2 a ha
    · have empty:J=∅:=Finset.not_nonempty_iff_eq_empty.mp hj
      subst J
      rw [legal.quiet' y,well.quiet' y]
      exact ⟨rfl,fun n r=>(plume_zero _).symm⟩
  refine ⟨hB,legal,files,?_⟩
  intro n y J a ha r
  by_cases hj:J.Nonempty
  · by_cases within:r ≤ mass k univ+e
    · have cmp:tariff G r s ≤ gross G (mass k univ+e) s 1:=by
        simpa only [mul_one] using (buys G within s (by norm_num : 0 ≤ (1:ℝ)))
      have bnd:tariff G r s*A^J.card ≤ B^J.card:=by
        dsimp only [B]
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (cmp.trans (le_self_pow₀ (one ..) (Nat.ne_of_gt (Finset.card_pos.mpr hj)))) (pow_nonneg positive _)
      rw [(files y J a ha).2 n r,(files y J a ha).1]
      exact (plumeW (cover y J a ha r) hj hs).more bnd
    · have sub:mass k J  ≤  mass k univ:=by unfold mass; exact sum_le_sum_of_subset (subset_univ _)
      have high:mass k J+a<r:=by omega
      rw [(legal.level' y J).span n a r high,(legal.level' y J).coverN a r high]
      exact MarkU.zero.more (pow_nonneg (zero_le_one.trans hB) _)
  · have empty:J=∅:=Finset.not_nonempty_iff_eq_empty.mp hj
    subst J
    rw [legal.quiet' y]
    exact MarkU.zero.more (pow_nonneg (zero_le_one.trans hB) _)

end YM.Integration.WilsonReceivedCompactVerseEntrance
