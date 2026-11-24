import YM.Integration.WilsonMovingForkSharpCaptured
import YM.Integration.WilsonSeparatedPrefixMovingNearReturn

/-! The two-region bound belongs to the actual reported local subtraction.
Choose the captured section by applying Mer's near-roster purchase on the
same published chart; its scalar and the counterterm page are explicit. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpBooking
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonSeparatedPrefixMovingLateLaw (whole)
open WilsonSeparatedPrefixMovingWages (coupon)
open scoped BigOperators Topology Classical

variable {G:Gauge}{h D k n:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}

def Hearing {a u k' e:ℕ}{v:Rails h k (u+a) e}{E W K U:Credit}(Y:CutsP H T p v E W K U)
    (Q:SealR G)(V V' L L' C₀ C₁ C₂:Credit):Prop:=
    let R:=Y.vesselsC
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
          ((ratio^h*WilsonMovingForkSharpIncome.gain Y)*(residue+Z*(joins*C₂.buy Z)))

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(arms:Fin (n+1)→SealR G)(Q:SealR G)
    (a u extra k' e:ℕ)(v:Rails h k (u+a) e)(E W K U V V' L L' Wn Ln:Credit)(order:a=h+Q.h+extra)(spare:0<extra):
    ∃capture C₀ C₁ C₂:Credit,∀(torch:Torch H T p v E W K)(choir:ChorusLine H T p e E W U)
      (_same:choir.arch=torch.L),let R:=torch.L.V
      ∀(_arms:HorizonP H R W V' arms)(_near:SpringD R (capP arms) (u+a) (capP arms+2) Wn)
      (_dorm:Dormitory R (capP arms) (u+a) Ln)(t s m N:ℕ),
      R.anchor ≤ t → t+s ≤ m → m ≤ N → capP arms ≤ k →
      ∀(φ:Wilt arms)(X:Herit arms)(fees B:Fin (n+1)→ℝ)(Z δ:ℝ),
      PadRank R (t+s) m Z → Bough arms φ (paceT R.draws.S m (t+s)) Z B →
      R.tempC m m ≤ δ → Sitting arms fees e δ X X →
      let genuine:=AutumnDay R.draws R.paid φ X m (t+s) N D
      ∃Y:CutsP H T p v E W K U,
        Y.L=torch ∧ Y.L'=choir ∧ Y.vesselsC=R ∧ Y.N=N ∧ Y.m=t ∧ Y.i=s ∧ Y.pt=genuine ∧
        Y.fuel=max 0 (capture.buy Z*∏i,B i*fees i) ∧
        Reports R.draws R.paid T p φ X m (t+s) t N k=
          (paceT R.draws.S m (t+s))^h • steep R.draws R.paid T p N (t+s) (m-(t+s)) Y.tileP ∧
        Y.springP s=genuine-Shrine Y.Ntop Y.tileP ∧
        Hearing (k':=k') Y Q V V' L L' C₀ C₁ C₂:=by
  obtain ⟨capture,_,enter⟩:=WilsonSeparatedPrefixMovingNearReturn.original H T p v E W K U V' Wn Ln arms
  obtain ⟨C₀,C₁,C₂,older⟩:=WilsonMovingForkSharpCaptured.original H T p Q a u extra k' e
    v E W K U V V' L L' order spare
  refine ⟨capture,C₀,C₁,C₂,?_⟩
  intro torch choir same R roster spring dorm t s m N gate formed cutoff rank φ X fees B Z δ clock early fit claims
    genuine
  obtain ⟨Y,auth,quiet,cap,tm,si,pt,wage,reports,stable,_⟩:=enter torch choir same roster spring dorm t s m N
    gate formed cutoff rank φ X fees B Z δ clock early fit claims
  have eq:Y.vesselsC=R:=by change Y.L.L.V=torch.L.V;rw [auth]
  exact ⟨Y,auth,quiet,eq,cap,tm,si,pt,wage,reports,stable,older Y⟩

end YM.Integration.WilsonMovingForkSharpBooking
