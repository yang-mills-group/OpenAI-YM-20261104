import YM.Integration.WilsonOlderFreshSoftWord

/-! The complete fixed-child ordinary source on two older stops, on one appointed quiet bank. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOlderFreshSoftOrdinary
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
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] 

def material (D k:ι→ℕ)(L:Levels G)(O:ChartRatio G)(Y:Outerm G D)
    (N:ℕ)(cell:Digits L ι)(c K:ℕ)(y:ι → Cover)(T:Finset ι)(f:Pen D T→L[ℝ] ℝ):Era G ℝ:=
  tuftV f (levelsO (itinerary L O k N cell (K-c) c Y y) T)

theorem original (G:Gauge)(D k:ι→ℕ)(e:ℕ):
    ∃s:ℝ,1 ≤ s ∧ ∀(T:Finset ι),T.Nonempty → ∃U V:Credit,
      ∀(S:Realm G (e+1) Credit.leanC),Dormitory S (mass k T) 0 Credit.leanC →
      ∀(N K c w v:ℕ),S.anchor ≤ v → v ≤ w → w ≤ c → c ≤ K → K ≤ N →
      ∀(Z₀ Z:ℝ),PadRank S c K Z₀ → PadRank S v w Z →
      ∀(Y:Outerm G D),Wellness k Y → ∀d:ℝ,0≤d → (∀y T,shingled y T Y e 1 d) →
      ∀(cell:Digits S.draws ι)
        (y:ι → Cover)(f:Pen D T→L[ℝ] ℝ),‖f‖ ≤ 1 →
      let P:=material D k S.draws S.paid Y N cell c K y T f
      let k₀:=mass k T
      let H:=cruises S.draws S.paid N k₀ c w P
      let full:=cruises S.draws S.paid N k₀ c v P
      let deposit:=cruises S.draws S.paid N k₀ w v (scalarOnly H)
      let initial:=(WilsonIndependentCollarOrdinaryWeak.price G k₀ e).buy Z₀*(s*d)^T.card
      let fare:=S.cash U w*S.tempC w c*initial
      Auth k₀ P ∧ Saturation e 0 0 P.2 1 initial ∧ Saturation e 1 0 H.2 1 fare ∧
        Saturation e 0 0 (full-deposit).2 1 (V.buy Z*fare) ∧ ∀q ≤ e,∀g:ℝ,
          ‖WilsonOlderFreshHybridClock.flat full q g-flat deposit q g‖ ≤ (∑j∈range (q+1),|g|^j)*(V.buy Z*fare):=by
  obtain ⟨s,sp,seed⟩:=WilsonIndependentCollarSeedTariff.original G D k e
  refine ⟨s,sp,?_⟩
  intro T t
  obtain ⟨U,V,two⟩:=WilsonOlderFreshSoftStops.received G (mass k T) e 0 Credit.leanC Credit.leanC
  refine ⟨U,V,?_⟩
  intro S dorm N K c w v first vw wc cK KN Z₀ Z early late Y clean d dp shed cell y f fn P k₀ H full deposit initial fare
  have hi:=first.trans (vw.trans wc)
  have date:c+(K-c)=K:=by omega
  have cut:c+(K-c) ≤ N:=by omega
  have well:=sound S.draws S.paid k N cell S.hG S.green _ clean (K-c) c cut
  have lawful:Auth k₀ P:= (placedO _ (well.level' y) T).tuft f
  have crown:=seed _ clean d dp shed
    (address S.draws cell (K-c) c y) T t f fn
  have opening:Saturation e 0 0 P.2 1 initial:=by
    intro i ie r _
    have cash:=WilsonIndependentCollarOrdinaryWeak.scalar S N cell _ clean T (K-c) c y hi cut
      Z₀ ((s*d)^T.card) (date.symm ▸ early) (pow_nonneg (mul_nonneg (zero_le_one.trans sp)
        dp) _) dorm f crown i r ie
    simpa only [P,material,initial,k₀,Fruit,Award,hedge,autumn,pow_zero] using cash
  have amount:0 ≤ initial:=by
    have hz:=early.pos (oldGuard hi cK)
    exact mul_nonneg (zero_le_one.trans (Credit.purchase _ hz))
      (pow_nonneg (mul_nonneg (zero_le_one.trans sp) dp) _)
  obtain ⟨positive,heard⟩:=two S dorm v w c N Z initial first vw wc (cK.trans KN) late
    amount P lawful (fun i ie r _=>opening i ie r (Nat.zero_le _))
  exact ⟨lawful,opening,positive,heard,fun _ le g=>WilsonOlderFreshSoftWord.valued full deposit heard le g⟩

end YM.Integration.WilsonOlderFreshSoftOrdinary
end
