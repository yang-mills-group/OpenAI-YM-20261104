import YM.WilsonCoeffUV.Root.UV.FrameSupply
import YM.WilsonCoeffUV.Reclosure.Store
/-!
# Schedule demands grouped on one dictionary. No cross-theory matches. z= true log log.
Reads against compatible steps, all fine levels. Economic pre-floor uses stencil frame fixed before constructing Sheet;
not chosen from existential separately. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos.Polestar
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Supply Ticket Next.Foundations
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V:Type*}{r h D l e j k a N M m b i q z:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{A A':Levels G}{Ñ:ChartRatio G}

-- mains all; same fields own-horizon independent.
variable {p:Sheet G}{Q:Rolls p}{Ω:Protection Q}{F' D':ℕ→ℕ} {Y:Delays Ω}{o:Bar Y}{b':Supply.Wait o}
lemma ripe (H:Hol G)(R:Master H)(g:G.Simple)(hA:LocalRatio Ñ)(pL:floors G p.kernel F'≤ p.floorL)(zL:(fun i=>sharp H R p.kernel Ñ i (F' i) (D' i))≤ p.floorL)(a:Paid b' A)(hp:voucher Q F' Ñ≤ Y.betaEntry)(hz:(fun j=>tickZ H R p.kernel Ñ (Q.L j) (F' j) (D' j) j)≤ Y.betaEntry)(hF:Tendsto F' atTop atTop)(hD:Tendsto D' atTop atTop)(e:ℕ)(q:h<D):
    ∀ᶠ m:ℕ in atTop,∃ S:ChorusLine H (R.T h) q e Credit.leanC Credit.leanC Credit.leanC, S.arch.V.draws=A ∧ S.arch.V.paid=Ñ ∧ S.arch.V.y=zz A ∧ S.arch.V.anchor=m:=by
    have he: Tendsto (fun i=>A.clock.J (i+1)) atTop atTop:= A.fits.deep.comp (tendsto_add_atTop_nat 1)
    obtain ⟨v,hv⟩:= eventually_atTop.mp ((he.eventually_ge_atTop (max 5 (h+3))).and (((hF.comp he).eventually_ge_atTop (e+1)).and ((hD.comp he).eventually_ge_atTop D)))
    refine (eventually_ge_atTop v).mono (fun i hi=> fixtures H R g hA pL zL a hp hz q e i (fun k hk=>?_));
    obtain ⟨x,t⟩:=hv k (hi.trans hk); exact ⟨by omega,by omega,t⟩

-- strengthened Levels existence witness (arbitrary): independent-history application. Includes choice of YY strengthening for curvature.
theorem sanction (H:Hol G)(R:Master H)(Ñ:ChartRatio G)(q:LocalRatio Ñ)(u:ℝ)(hu:0<u)(g:G.Simple) : ∃ p: Sheet G, p.kernel.penalty=u ∧ Nonempty (Rolls p) ∧∀ W:Rolls p,∃ T:Protection W,∃ Y:Delays T,∃ o:Bar Y, Nonempty (Supply.Wait o) ∧∀ B:Supply.Wait o, (∃ A:Levels G,Paid B A) ∧ ∀ (A:Levels G), Paid B A →
       (∀ e:ℕ,∀ᶠ m in atTop, ∃ S:Realm G e Credit.leanC, S.draws=A ∧ S.paid=Ñ ∧ S.y=zz A ∧ S.anchor=m ∧ Mosaic.Inkplate e S Credit.leanC) ∧
       (∀ e h D:ℕ,∀ p:h<D,∀ᶠ m in atTop,∃ S:ChorusLine H (R.T h) p e Credit.leanC Credit.leanC Credit.leanC,S.arch.V.draws=A ∧ S.arch.V.paid=Ñ ∧ S.arch.V.y=zz A ∧ S.arch.V.anchor=m) :=by
    let X:= @id ℕ
    let K:= Next.Foundations.kernel G u hu
    have he:= Next.Foundations.branches G u hu
    obtain ⟨T⟩:= cap_st
    let p: Sheet G:= ⟨K,he,fun _=>T,5,by omega,monotone_const,monotone_const,monotone_const,(floors G K X ⊔ fun i=>sharp H R K Ñ i (X i) (X i))⟩
    have hP: floors G K X≤p.floorL:=le_sup_left
    have hp:(fun i=> sharp H R K Ñ i (X i) (X i))≤ p.floorL:= le_sup_right
    refine ⟨p,(Axial.viable G u hu).choose_spec.1,Rolls.exists_rolls p g,fun W=>?_⟩
    obtain ⟨t,h⟩:= Protection.exists_margin W (fun _=>1) (fun _=>one_pos)
    let L j:=tickZ H R K Ñ (W.L j) (X j) (X j) j
    let V:= voucher W X Ñ
    let Z:= Mosaic.accountZ K X Ñ
    let Y: Delays t:= ⟨Z⊔(V⊔ L),0,0,0⟩
    have hY : V≤Y.betaEntry:= le_trans (le_sup_left (b:=L)) le_sup_right
    obtain ⟨o,h'⟩:= Bar.exists_above Y 1
    exact ⟨t,Y,o,⟨0,fun _ _=>0,fun _=>by simp,0⟩,fun B=> ⟨Wait.ready B g,fun A a=> ⟨ Mosaic.proceeds (p:=p) (b':=B) (H:=X) g q hP a hY (show Z ≤ Y.betaEntry from (show Z≤ Z⊔(V⊔ L) from le_sup_left)) tendsto_id,fun e h D p'=> ripe (p:=p) (F':=X) (D':=X) H R g q hP hp a hY (show L≤ Y.betaEntry from le_trans (le_sup_right (a:=V)) le_sup_right) tendsto_id tendsto_id e p'⟩⟩⟩

def primes (G : Gauge): Master (Next.Foundations.hol G) := ⟨_, Next.Foundations.localSection G, Next.Foundations.sound G, Next.Foundations.valuation G ⟩
lemma gauges (g:G.Simple) (u:ℝ) (p:0<u): ∃ A: Levels G, A.clock.kernel.penalty=u ∧∀ e h D:ℕ,∀ p:h<D,∀ᶠ m in atTop,∃ S:ChorusLine (Next.Foundations.hol G) ((primes G).T h) p e Credit.leanC Credit.leanC Credit.leanC, S.arch.V.draws=A ∧ S.arch.V.paid= Next.Foundations.chart G ∧ S.arch.V.y=zz A ∧ S.arch.V.anchor=m:=by
    obtain ⟨S,hS,⟨W⟩,f⟩:= sanction _ (primes G) _ (Next.Foundations.chart_ok G) u p g
    obtain ⟨T,Y,o,⟨B⟩,hB⟩:= f W
    obtain ⟨A,v⟩:= (hB B).1
    exact ⟨A,v.kernel ▸ hS,fun i=>( (hB B).2 A v).2 i⟩
end YM.WilsonCoeffUV.Cosmos.Polestar
