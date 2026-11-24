import YM.Integration.WilsonSeparatedPrefixMovingNearReturn
import YM.Integration.WilsonSeparatedPrefixMovingOwnDate

/-! A first join after capture. The near source includes the old scalar
and is the complete propagated difference on its own nominated chart.
The reflected exterior enters as its literal own-date normalized column. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingLaterJoin
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

variable {G:Gauge}{h D a k k' e u extra:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {E W K U V V' L:Credit}

/-- Display the surviving inverse exterior radius before applying any matrix
inverse. This equality retains the entire native block length. -/
theorem degree (x ratio Lb s A:ℝ)(hx:0<x)(hl:0<ratio)(hL:0<Lb)(hs:0<s)(d w r:ℕ):
    ((s/(x*Lb))^(d+w+r))⁻¹*((x^d)⁻¹*ratio^d*((x^w)⁻¹*A)) =
      ratio^d*((Lb/s)^(d+w+r)*x^r*A):=by
  simp only [div_pow,mul_pow,pow_add]
  field_simp

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(Q:SealR G)
    (a u extra k' e:ℕ)(v:Rails h k (u+a) e)(E W K U V V' L:Credit)
    (_moment:a=h+Q.h+extra):
    ∃C₀ C₁:Credit,∀(Y:CutsP H T p v E W K U),let R:=Y.vesselsC
      ∀(_far:PassportC H R Q W V'),SpringD R k' u a V → Dormitory R (k+Q.h) u L →
      ∀ z t earlier, z<Y.i → t≤Y.m+z → k+Q.h≤k' →
      ∀(Z₀ Z₁:ℝ),Compar R.draws.S R.y t (Y.m+z+1)≤Z₁ → R.anchor≤t →
      ∀(η:ℕ→ℝ),Escort R earlier (Y.m+z) η → PadRank R earlier (Y.m+z) Z₀ →
      ∀(φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)(y dist radius Bφ Bψ:ℝ)(o:CellR),
      let i:=Y.m+z
      let x:=paceT R.draws.S t (i+1)
      let P:=ll R.draws i
      let ratio:=paceT R.draws.S t Y.ceilC
      let b:=u+a
      let far:=locale o (Q.spins R.draws R.paid ψ t (i+1) Y.N y X)
      let near:=word (ratio^h • Y.springP (z+1)) φ x y o h
      let born:=JoinGap R.draws R.paid i Y.N k Q.h near far
      let arrived:=cruises R.draws R.paid Y.N (k+Q.h) i earlier born
      let α:=(polarBill H Q.ans Q.path e b E W V').choose
      let nearFee:=(5*radiusH φ x y)^4*(9^b*(Bφ*price Y C₀ (z+1) 1))
      let farFee:=(5*radiusH ψ x y)^4*(9^b*(Bψ*(α.buy Z₁*WilsonSeparatedPrefixMovingOwnDate.fee Q e X)))
      (η i=x*P.L.val) → ClearDay φ ψ dist → 0<dist → radiusH φ (x*P.L.val) y≤radius →
      radiusH ψ (x*P.L.val) y≤radius → (VisitsT φ x y o).Nonempty →
      (VisitsT ψ x y o).Nonempty → Amplitude φ Bφ → Amplitude ψ Bψ →
      let salary:=ratio^h*(C₁.buy Z₀*(R.cash (priceWG G e k' u a E V) i*
        ((16*radius)^u*((P.L.val/dist)^a*x^extra*(nearFee*farFee)))))
      verseI R.draws R.paid i Y.N (k+Q.h) (agateV near far)=
        born+agateV (verseI R.draws R.paid i Y.N k near) (verseI R.draws R.paid i Y.N Q.h far) ∧
      Flush e u (η earlier) arrived salary ∧ ∀ grade≤e,∀ ω:Fin 0→YForest G,
        ‖arrived.2 grade 0 ω‖≤salary:=by
  obtain ⟨C₀,posts⟩:=WilsonIndependentMatchedCoverProfile.original H T p v E W K U
  obtain ⟨C₁,older⟩:=WilsonIndependentMatchedCoverJoined.original G k Q.h k' e u a E V L
  refine ⟨C₀,C₁,?_⟩
  intro Y R outer spring dorm z t earlier active late seat Z₀ Z₁ clock origin η route room
    φ ψ X y dist radius Bφ Bψ o i x P ratio b far near born arrived α nearFee farFee
    scale clear separated nearBound farBound nearSeen farSeen nearPrice farPrice salary
  have xi:0<x:=pace_pos ..
  have lp:0<ratio:=pace_pos ..
  have lpos:0<(P.L.val:ℝ):=by exact_mod_cast P.L.pos
  have edge:i<Y.N:=lt_of_lt_of_le (Nat.add_lt_add_left active _) (Y.hc.trans Y.hn)
  have ix:t ≤ i+1:=late.trans (Nat.le_succ _)
  have larger:x*P.L.val=paceT R.draws.S t i:=pace_step ..
  have payX:=posts Y (z+1) active (ratio^h) φ x y o h P xi (pace_le _ ix) Bφ nearPrice
  have payFar:=WilsonSeparatedPrefixMovingOwnDate.column outer t (i+1) Y.N b origin ix edge Z₁ clock
    X ψ y o P Bψ farPrice
  have sold:=older R spring dorm earlier i (i+1) Y.N (origin.trans late) (Nat.lt_succ_self _)
    edge seat η Z₀ route room φ ψ near far x y dist radius o xi (larger ▸ pace_le _ late) scale
    clear separated nearBound farBound nearSeen farSeen _ _ payX payFar
  have chargeX:charge φ b h x y (price Y C₀ (z+1) (ratio^h)) Bφ=(x^h)⁻¹*ratio^h*nearFee:=by
    rw [WilsonSeparatedPrefixMovingOwnDate.units]
    dsimp only [nearFee,WilsonIndependentMatchedCoverProfile.price]
    rw [abs_of_pos (pow_pos lp _),abs_one]
    ring
  have chargeF:charge ψ b Q.h x y (α.buy Z₁*WilsonSeparatedPrefixMovingOwnDate.fee Q e X) Bψ=
      (x^Q.h)⁻¹*farFee:=WilsonSeparatedPrefixMovingOwnDate.units ..
  dsimp only at sold
  change _ ∧ Flush e u (η earlier) arrived _ ∧ _ at sold
  have bill:C₁.buy Z₀*(R.cash (priceWG G e k' u a E V) i*
      (pearlB u a (4*radius) (dist/η i)*
        (charge φ b h x y (price Y C₀ (z+1) (ratio^h)) Bφ*
        charge ψ b Q.h x y (α.buy Z₁*WilsonSeparatedPrefixMovingOwnDate.fee Q e X) Bψ)))=salary:=by
    rw [chargeX,chargeF,scale]
    dsimp only [pearlB,salary]
    have gain:=degree x ratio P.L.val dist (nearFee*farFee) xi lp lpos separated h Q.h extra
    rw [←_moment] at gain
    linear_combination C₁.buy Z₀ * R.cash (priceWG G e k' u a E V) i*(4*(4*radius))^u*gain
  rw [bill] at sold
  exact sold

end YM.Integration.WilsonSeparatedPrefixMovingLaterJoin
