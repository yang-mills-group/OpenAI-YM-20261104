import YM.Integration.WilsonOlderFreshSoftStops
import YM.Integration.WilsonIndependentCollarOrdinaryWeak
import YM.Integration.WilsonIndependentCollarSeedTariff
import YM.Integration.WilsonIndependentCollarPointBill

/-! Two older independent hearings of one ordinary canonical point entry.
The initial word and its unit use the same true digit at every date on the original top quiet. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOlderFreshSoftWord
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonCoeffUV.Soil
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Power WilsonCoeffUV.Shard WilsonCoeffUV.Fountain
open PhysicalNext.Repeat.Legato OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonThermometerDeclaredSeeds (Choice)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedFixedDigitHistory (Digits itinerary sound)
open WilsonIndependentCollarOrdinaryCruise (address)
open WilsonOlderFreshHybridClock (flat)
open WilsonOlderFreshSoftStops (scalarOnly)
open scoped Classical BigOperators
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] {e:ℕ}

theorem valued (P Q:Era G ℝ){A:ℝ} (cash:Saturation e 0 0 (P-Q).2 1 A){q:ℕ}(kept:q ≤ e)(g:ℝ):
    ‖WilsonOlderFreshHybridClock.flat P q g-flat Q q g‖ ≤ (∑j∈range (q+1),|g|^j)*A:=by
  unfold WilsonOlderFreshHybridClock.flat WilsonOlderFreshTerminalProgramme.series
  rw [←sum_sub_distrib,sum_mul]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro j hj
  have pay:=cash j (by have h:=mem_range.mp hj;omega) 0 (by omega)
  have one:=pay.2.1.sum_le_tsum ({Fin.elim0}:Finset (dock Cover _ 0)) (fun i _ =>pay.1 i)
  rw [sum_singleton] at one
  have cell:‖P.2 j 0 Fin.elim0-Q.2 j 0 Fin.elim0‖ ≤ A:=by
    simpa only [hedge,autumn,pow_zero,one_mul,Prod.snd_sub,Pi.sub_apply] using one.trans pay.2.2
  rw [←mul_sub,norm_mul,Real.norm_eq_abs,abs_pow]
  exact mul_le_mul_of_nonneg_left cell (by positivity)

def material (R:Run G)(D k:ι→ℕ)(L:Levels G)(O:ChartRatio G)
    (κ:(j:ι)→Knob (D j))(pt:ι→Chamber)(a:(j:ι)→Choice R k j)
    (N:ℕ)(cell:Digits L ι)(c K:ℕ)(y:ι → Cover)(T:Finset ι)(f:Pen D T→L[ℝ] ℝ):Era G ℝ:=
  tuftV f (levelsO (itinerary L O k N cell (K-c) c (start R k κ pt a) y) T)

theorem original (R:Run G)(D k:ι→ℕ)(e:ℕ):
    ∃B:ℝ,1 ≤ B ∧ ∀(T:Finset ι),T.Nonempty → ∃U V:Credit,
      ∀(S:Realm G (e+1) Credit.leanC),Dormitory S (mass k T) 0 Credit.leanC →
      ∀(N K c w v:ℕ),S.anchor ≤ v → v ≤ w → w ≤ c → c ≤ K → K ≤ N →
      ∀(Z₀ Z:ℝ),PadRank S c K Z₀ → PadRank S v w Z →
      ∀(κ:(i:ι)→Knob (D i))(pt:ι→Chamber)(a:(i:ι)→Choice R k i)(cell:Digits S.draws ι)
        (y:ι → Cover)(f:Pen D T→L[ℝ] ℝ),‖f‖ ≤ 1 →
      let P:=material R D k S.draws S.paid κ pt a N cell c K y T f
      let k₀:=mass k T
      let H:=cruises S.draws S.paid N k₀ c w P
      let full:=cruises S.draws S.paid N k₀ c v P
      let deposit:=cruises S.draws S.paid N k₀ w v (scalarOnly H)
      let initial:=(WilsonIndependentCollarOrdinaryWeak.price G k₀ e).buy Z₀*B^T.card
      let fare:=S.cash U w*S.tempC w c*initial
      Auth k₀ P ∧ Saturation e 0 0 P.2 1 initial ∧ Saturation e 1 0 H.2 1 fare ∧
        Saturation e 0 0 (full-deposit).2 1 (V.buy Z*fare) ∧ ∀q ≤ e,∀g:ℝ,
          ‖WilsonOlderFreshHybridClock.flat full q g-flat deposit q g‖ ≤ (∑j∈range (q+1),|g|^j)*(V.buy Z*fare):=by
  obtain ⟨d,dp,source⟩:=WilsonIndependentCollarPointBill.original R D k e (w:=1) zero_lt_one
  obtain ⟨s,sp,seed⟩:=WilsonIndependentCollarSeedTariff.original G D k e
  refine ⟨s*d,one_le_mul_of_one_le_of_one_le sp dp,?_⟩
  intro T t
  obtain ⟨U,V,two⟩:=WilsonOlderFreshSoftStops.received G (mass k T) e 0 Credit.leanC Credit.leanC
  refine ⟨U,V,?_⟩
  intro S dorm N K c w v first vw wc cK KN Z₀ Z early late κ pt a cell y f fn P k₀ H full deposit initial fare
  have issued:=source κ pt a
  have hi:=first.trans (vw.trans wc)
  have date:c+(K-c)=K:=by omega
  have cut:c+(K-c) ≤ N:=by omega
  have well:=sound S.draws S.paid k N cell S.hG S.green _ issued.1 (K-c) c cut
  have lawful:Auth k₀ P:= (placedO _ (well.level' y) T).tuft f
  have crown:=seed _ issued.1 d (zero_le_one.trans dp) issued.2
    (address S.draws cell (K-c) c y) T t f fn
  have opening:Saturation e 0 0 P.2 1 initial:=by
    intro i ie r _
    have cash:=WilsonIndependentCollarOrdinaryWeak.scalar S N cell _ issued.1 T (K-c) c y hi cut
      Z₀ ((s*d)^T.card) (date.symm ▸ early) (pow_nonneg (mul_nonneg (zero_le_one.trans sp)
        (zero_le_one.trans dp)) _) dorm f crown i r ie
    simpa only [P,material,initial,k₀,Fruit,Award,hedge,autumn,pow_zero] using cash
  have amount:0 ≤ initial:=by
    have hz:=early.pos (oldGuard hi cK)
    exact mul_nonneg (zero_le_one.trans (Credit.purchase _ hz))
      (pow_nonneg (mul_nonneg (zero_le_one.trans sp) (zero_le_one.trans dp)) _)
  obtain ⟨positive,heard⟩:=two S dorm v w c N Z initial first vw wc (cK.trans KN) late
    amount P lawful (fun i ie r _=>opening i ie r (Nat.zero_le _))
  exact ⟨lawful,opening,positive,heard,fun _ le g=>valued full deposit heard le g⟩

end YM.Integration.WilsonOlderFreshSoftWord
end
