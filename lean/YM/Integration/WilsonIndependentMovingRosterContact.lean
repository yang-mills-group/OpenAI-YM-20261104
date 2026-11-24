import YM.Integration.WilsonSeparatedPrefixMovingSecondBirth

/-! A complete deposited near field meets the genuinely normalized exterior
at its own date. The near income may come from a roster of any arity. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterContact
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

theorem original {G:Gauge}{e:ℕ}{H:Hol G}{E W V:Credit}(R:Realm G (e+1) E)
    (Q:SealR G)(h k u a target left extra D:ℕ)(wave:a=Q.h+extra)(decay:a=u+Q.h+target+left)
    (spring:SpringD R k u a W)(outer:PassportC H R Q W V)(t m i N:ℕ)
    (live:R.anchor ≤ t)(home:t ≤ m)(fine:m ≤ i)(edge:i < N)(room:Q.h+h ≤ k)
    (near:Era G ℝ)(χ:Rarity D)(ψ:Rarity Q.D)(w:Q.Rider)(y gap radius Z innerFee Bψ:ℝ)(o:CellR):
    let T:=paceT R.draws.S m t
    let x:=paceT R.draws.S m (i+1)
    let P:=ll R.draws i
    let η:=x*P.L.val
    let far:=locale o (Q.spins R.draws R.paid ψ t (i+1) N (y/T) w)
    let second:=JoinGap R.draws R.paid i N Q.h h far near
    let outerFee:=WilsonSeparatedPrefixMovingFineFare.unitFee (H:=H) (E:=E) (W:=W)
      (V:=V) (e:=e) (b:=u+a) Q w ψ Z (x/T) (y/T) Bψ
    Income near h e (u+a) (OrbP P χ x y o) innerFee → Compar R.draws.S R.y t (i+1) ≤ Z →
    Amplitude ψ Bψ → 0 < gap → (0:Cover)∈VisitsT χ x y o →
    (∀p∈tsupport χ.ψ.val,∀q∈tsupport ψ.ψ.val,T*gap ≤ dist p (T • q)) →
    radiusH χ η y ≤ radius → radiusH ψ (η/T) (y/T) ≤ radius →
    (VisitsT ψ (x/T) (y/T) o).Nonempty →
    Auth (Q.h+h) second ∧ Flush e u η second
      (R.cash (priceWG G e k u a E W) i*(((T^target)⁻¹*(T^left)⁻¹*x^extra*
        ((16*radius)^u*((P.L.val:ℝ)/gap)^a))*(outerFee*innerFee))):=by
  intro T x P η far second outerFee p clock paid gapPos center separate nearBox farBox farLive
  have f:=WilsonSeparatedPrefixMovingOwnDate.column outer t (i+1) N (u+a) live
    (home.trans (fine.trans (Nat.le_succ _))) (by omega) Z clock w ψ (y/T) o P Bψ paid
  rw [WilsonSeparatedPrefixMovingUnformed.rulers R.draws.S t m (i+1)] at f
  have bound:η≤1:=by change paceT R.draws.S m (i+1)*(R.draws.S.block i).val≤1;rw [pace_step];exact pace_le _ fine
  have zoom:1≤T:=pace_ge _ home
  have dom:radius≤T*radius:=le_mul_of_one_le_left ((zero_le_one.trans (fieldCap χ η y)).trans nearBox) zoom
  have z:η/T=x/T*P.L.val:=by dsimp only [η];ring
  have apart:=WilsonSeparatedPrefixMovingLenses.original P χ ψ x y T (T*gap) radius radius o
    (pace_pos ..) zoom bound (mul_pos (pace_pos ..) gapPos) separate nearBox (z ▸ farBox) ⟨0,center⟩ farLive
  let δ:=max (0:ℝ) (δWarm R i N)
  have grant:=enterShore spring (live.trans (home.trans fine)) (show i<N by omega) le_rfl le_rfl
    far far near near f.1 f.1 p.1 p.1 apart room (le_max_right (0:ℝ) _)
    (f.2 δ (le_max_left _ _)) (p.2 δ (le_max_left _ _))
  refine ⟨grant.pen,?_⟩
  have fee:=grant.f_l
  change Flush e u η second (R.cash (priceWG G e k u a E W) i *
    (pearlB u a (4*max radius (T*radius)) (T*gap/η)*
       (WilsonSeparatedPrefixMovingUnformed.fare H E W V Q w ψ e (u+a) Z (x/T) (y/T) Bψ*
         innerFee))) at fee
  have outerCost:WilsonSeparatedPrefixMovingUnformed.fare H E W V Q w ψ e (u+a) Z (x/T) (y/T) Bψ=
      ((x/T)^Q.h)⁻¹*outerFee:=WilsonSeparatedPrefixMovingOwnDate.units ..
  rw [max_eq_right dom,outerCost] at fee
  let pref:=pearlB u a (4*(T*radius)) (T*gap/η)
  have price:=WilsonSeparatedPrefixMovingFineFare.powers u a 0 Q.h target left extra
    (by simpa only [Nat.zero_add] using wave) decay x (P.L.val:ℝ) T gap radius
    (pace_pos ..) (by exact_mod_cast P.L.pos) (pace_pos ..) gapPos
  simp only [pow_zero,inv_one,mul_one] at price
  change pref*(((x/T)^Q.h)⁻¹)=_ at price
  have arrangement:pref*((((x/T)^Q.h)⁻¹*outerFee)*innerFee)=
      (pref*((x/T)^Q.h)⁻¹)*(outerFee*innerFee):=by ring
  change Flush e u η second (_*(pref*((((x/T)^Q.h)⁻¹*outerFee)*innerFee))) at fee
  rw [arrangement,price] at fee
  exact fee

end YM.Integration.WilsonIndependentMovingRosterContact
