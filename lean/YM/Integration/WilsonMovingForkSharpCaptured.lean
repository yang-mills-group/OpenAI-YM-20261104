import YM.Integration.WilsonMovingForkSharpUnjoined
import YM.Integration.WilsonMovingForkSharpJoins
import YM.Integration.WilsonSeparatedPrefixMovingHighGrades

/-! On the true normalized Mer source, the complete captured near remainder
and the actual exterior have one older scalar. Charge all its coupling
grades together with the physical power of the same exterior ruler. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpCaptured
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonSeparatedPrefixMovingLateLaw (whole birth)
open WilsonSeparatedPrefixMovingWages (coupon)
open Finset
open scoped BigOperators Topology Classical

variable {G:Gauge}{h D k:ℕ}{F:Labels.Frame G h}

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(Q:SealR G)(a u extra k' e:ℕ)
    (v:Rails h k (u+a) e)(E W K U V V' L L':Credit)(order:a=h+Q.h+extra)(spare:0<extra):
    ∃C₀ C₁ C₂:Credit,∀(Y:CutsP H T p v E W K U),let R:=Y.vesselsC
      ∀(_far:PassportC H R Q W V')(_P:SpringD R k' u a V)(_old:Dormitory R (k+Q.h) u L)
      (_end:Dormitory R (k+Q.h) (u+a) L')(older:ℕ)(_gate:R.anchor≤older)(_route:older≤Y.m)(_room:k+Q.h≤k')
      (φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)(y dist r Bφ Bψ:ℝ)(o:CellR),
      let Z:=epoch R older Y.ceilC
      let Z₁:=max Z (max ψ.radius |y|)
      let ratio:=paceT Y.ax.S Y.m Y.ceilC
      let nearFee:=BasePrice h φ 1 y*((1+4*radiusH φ 1 y)^(u+a)*(Bφ*(C₀.buy Z*Y.fuel)))
      let farFee:=(hardCash e (u+a) E W V' H Q).buy Z₁*(Bψ*WilsonSeparatedPrefixMovingOwnDate.fee Q e X)
      let residue:=C₁.buy Z*(coinMat (k+Q.h) e*nearFee*farFee)
      let joins:=(16*r)^u*(dist⁻¹)^a*((5*r)^4*(9^(u+a)*(Bφ*Y.fuel)))*coupon Q X e (u+a) r Bψ
      Amplitude φ Bφ → Amplitude ψ Bψ → ClearDay φ ψ dist → 0<dist →
      φ.radius+|y|+1≤r → ψ.radius+|y|+1≤r →
      ∀ω:Fin 0→YForest G,let page:=fun j=>(whole Y Q φ ψ X y o older Y.i).2 j 0 ω
      (∀q≤e,‖page q‖≤(ratio^h*WilsonMovingForkSharpIncome.gain Y)*(residue+Z*(joins*C₂.buy Z))) ∧
      ∀(J:ℕ)(g:ℝ),0≤g → g≤1 →
        ‖WilsonSeparatedPrefixMovingHighGrades.above J e g page‖≤((e+1:ℕ):ℝ)*g^(J+1)*
          ((ratio^h*WilsonMovingForkSharpIncome.gain Y)*(residue+Z*(joins*C₂.buy Z))):=by
  obtain ⟨C₀,C₁,full⟩:=WilsonMovingForkSharpUnjoined.original H T p Q v E W K U V' L'
  obtain ⟨C₂,sumDue⟩:=WilsonMovingForkSharpJoins.original H T p Q a u extra k' e v
    E W K U V V' L order spare
  refine ⟨C₀,C₁,C₂,?_⟩
  intro Y R ticket spring dorm terminal older gate road room φ ψ X y dist r Bφ Bψ o Z Z₁ ratio nearFee farFee
    residue joins own peer separate positive nearBox farBox ω page
  have law:=WilsonSeparatedPrefixMovingLateLaw.original Y Q ticket φ ψ X y o older road
  have held:∀q≤e,‖page q‖≤(ratio^h*WilsonMovingForkSharpIncome.gain Y)*(residue+Z*(joins*C₂.buy Z)):=by
    intro q hq
    have head:=full Y ticket terminal older gate road φ ψ X y Bφ Bψ o own peer q hq ω
    have later:=sumDue Y ticket spring dorm older gate road room φ ψ X y dist r Bφ Bψ o own peer
      separate positive nearBox farBox q hq ω
    change ‖(whole Y Q φ ψ X y o older 0).2 q 0 ω‖≤(ratio^h*WilsonMovingForkSharpIncome.gain Y)*residue at head
    change ‖∑j∈range Y.i,(birth Y Q φ ψ X y o older j).2 q 0 ω‖≤Z*(ratio^h*WilsonMovingForkSharpIncome.gain Y)*(joins*C₂.buy Z) at later
    have projected:=congrArg (fun x:Era G ℝ=>x.2 q 0 ω) law
    simp only [Prod.snd_add,Pi.add_apply,Prod.snd_sum,Finset.sum_apply] at projected
    change ‖(whole Y Q φ ψ X y o older Y.i).2 q 0 ω‖≤_
    rw [projected]
    calc
      _ ≤ (ratio^h*WilsonMovingForkSharpIncome.gain Y)*residue+Z*(ratio^h*WilsonMovingForkSharpIncome.gain Y)*(joins*C₂.buy Z):=(norm_add_le ..).trans (add_le_add head later)
      _=(ratio^h*WilsonMovingForkSharpIncome.gain Y)*(residue+Z*(joins*C₂.buy Z)):=by ring
  refine ⟨held,?_⟩
  intro J g gp small
  let bill:=(ratio^h*WilsonMovingForkSharpIncome.gain Y)*(residue+Z*(joins*C₂.buy Z))
  have paid:0≤bill:=(norm_nonneg (page 0)).trans (held 0 (Nat.zero_le _))
  have final:=WilsonSeparatedPrefixMovingHighGrades.original J e 0 g 1 bill page gp small zero_lt_one paid
    (fun q _ hq=>by simpa only [pow_zero,inv_one,one_mul] using held q hq)
  simpa only [pow_zero,inv_one,one_mul,mul_assoc,bill] using final

end YM.Integration.WilsonMovingForkSharpCaptured
