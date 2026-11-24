import YM.WilsonCoeffUV.Emit.FineLog
/-!
# Report interface for independent Fk as Λ-window estimate

Use tilted primary inputs X with *own* heights. Choose Ψ,.D from same field master.
Realm/supply versions discharged for every fixed shape horizon/orders and pre-width
order on `established`/`stars`/`paidSoft`. No real factors are reexpanded here.
No issue of MS or Gram, quotients, nested far scales, phases. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.Layout
open Wheel Wheel.ScaleS Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost Physical
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Wheel.Flooring Ticket
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{E B W V U: Credit}{m b N j a k u h D e:ℕ}{R:Realm G (e+1) E}{F:Frame G h}

/-- Every announced geometry and all fixed finite positive/zero output orders.
Comparisons on wider geometry/separation costs (`Bough`, includes arbitrary derivative amplitudes q(r))
see `reportUV`. Inputs P admissible as well beyond Λ^B power used here. `Scenery`
can use arbitrary A_i seminorms (transformed tests in sup coordinates); cutoff
chosen later with arbitrary exponential-in-Λ savings. -/
theorem on_shapes (H:Hol G) (T:SectionData F)(p:h<D) (Q: Fin (a+1)→SealR G)(w:Rails h k u e)
    (_q:capP Q≤k)
    (A₁ A₂ B C L E P: Credit)(d:ℝ)(R0:ℕ)
    :∃ A:Credit,∀ (Y:Torch H T p w E A₁ A₂)(R:ChorusLine H T p e E A₁ B), R.arch=Y.L → let M:= Y.L.V;
    HorizonP H M A₁ B Q → SpringD M (capP Q) u (capP Q+2) C → Dormitory M (capP Q) u L → M.y=zz M.draws→ ∀ m b j r (ρ:1≤r)(Φ:Wilt Q)(X:ℕ→ Herit Q)(B W': Fin (a+1)→ℝ), r≤ P.buy (longLog M.draws m) → Windows M.draws M.anchor m b j r → Scenery Q Φ R0 d B → Shipment M.draws.S m Q W' e X →
    ∀ i≤ e,∀ l:Alma F,
    let P0:= A.buy (longLog M.draws m)*(∏ i,(r⁻¹^4*B i)*W' i); let V':= coeff i (lodgeIn M.draws M.paid T p (sceneGrow ρ Φ) X m b j k l);
    let Vn:= fun N=> coeff i (Reports M.draws M.paid T p (sceneGrow ρ Φ) (X N) m b j N k l)
    Tendsto Vn atTop (𝓝 V') ∧ ∀ N M':ℕ,m ≤ N → N ≤ M' → twain P0 (M.tempC m N) (Vn M') V':=by
    obtain ⟨U',f⟩:=reportUV H Q T p w _q E A₁ A₂ B C L; obtain ⟨Z,g⟩:= bough_bill (V:=E) (e:=e+1) (G:=G) (a:=a) P d R0; refine ⟨U'.usingC Z,?_⟩; intro Y R z M H' S K he m b j r ρ Φ X B' W' u v q x i hv l; obtain ⟨s0,s1⟩:= g Q M he _ _ _ _ _ v ρ Φ B' u v.atBase q; simp only [Credit.stock_up]; exact f Y R z H' S K m b j (sceneGrow ρ Φ) X W' _ _ v.atBase v.soft.le v.capture.le s1 s0 x i hv l

/-- Spectator apertures in EXP true invoice. Includes separated mixed reaching
*k* even before opening. η costs `g_m^-η` relative via `exp_at_band`; flat
via `band_savings`. p replication and physical product estimates separate. -/
lemma analyticCapture (H:Hol G)(T:Fin (a+1)→SealR G)(P V E W L U:Credit)
    (e D B:ℕ)(d:ℝ)(q:0<d)(Z:ℝ)(u0:0<Z)
    :∃ Y:Credit,∀ (R:Realm G (e+1) E)(_z:R.y=zz R.draws)(_p:Tribe R H W V T),
    Cloze (fun i=>(T i).D) (fun i=>(T i).h) R U →
    ∀ᶠ m in atTop,∀ N a' b j r (Φ:Wilt T)(A W': Fin _→ℝ)(x:Herit T)(t:1≤r),
    m≤ N→ ∀ (_t:R.anchor≤ j) (_v:Windows R.draws a' m b j r),
    longLog R.draws m ^ 2 ≤ r → r≤ P.buy (longLog R.draws m)→
    Scenery T Φ B d A → (∀ i, 0<W' i) →
    (∀ i,sprouted (T i) (x i) e (W' i*L.buy (zz R.draws m))) →
    ∀ i≤e,∀ k, let ξ:=longLog R.draws m;
    Cork Bank.terrain 0 (Vσ R b (_t.trans _v.soft.le))
    ((∏ i,W' i)*(Real.exp (Y.buy (zz R.draws m))*(∏ i,r⁻¹^4*A i)))
    ((AutumnDay R.draws R.paid (sceneGrow t Φ) x m b N D).2 i k) ∧
    let η:= middle d r; let Q:= Gears R.draws R.paid (asp T) (asp T) N N m (coatA R.draws R.paid N m T x)
    ∀ v:Fin _ → Cover,∀ S:Finset (Fin _), cleared R.draws.S m m η v S → 1<S.card → Wig Bank.terrain v (R.mint m (((_t.trans _v.soft.le).trans _v.capture.le))).σ ((∏ i∈S,W' i)*Real.exp (- (Z*ξ))) S ((Q v S).2 i k):=by
    obtain ⟨C,g⟩:=portraits H T P V E W L U e d q; let X:=(invoke H T e E W V L U B).choose; refine ⟨X.usingC C,fun R z p h=>?_⟩
    filter_upwards [g R z,earned C U d q R.draws R.hG Z u0] with m hm he
    intro N a' b j r Φ A W' x t u hz M hp v H' E' l i hs k ξ; have hb:= hz.trans M.soft.le; have h': R.anchor≤ m:= hb.trans M.capture.le; let Z':= C.buy (zz R.draws m); obtain ⟨T',K,K'⟩:= hm b j a' r M B Φ A t hz hp v H'
    have hx:= K'.year m M.capture.le le_rfl; have hX0:1≤ zz R.draws m:= by rw [←z]; exact R.depth m h'
    have hx':zz R.draws m ≤ Z':=z ▸ hx; have hL i: sprouted (T i) (x i) e (W' i*L.buy Z'):=fun k g x=> (l i _ g x).trans (mul_le_mul_of_nonneg_left (L.elder hX0 hx') (E' i).le)
    constructor
    · rw [Credit.stock_up]; exact capture_exp x (sceneGrow t Φ) p W' E' L M.capture.le u hb K h K' T' hL hs k D
    intro η Q v' S δ ht; refine (crossing x W' p L E' h' u hx K hL h v' S ht le_rfl u δ hs k).more ?_; have h:=he r hp m (le_refl m); rw [snowP,sub_self,zero_div,Real.exp_zero,mul_one] at h; rw [snowP,sub_self]; exact mul_le_mul_of_nonneg_left h (Finset.prod_nonneg (fun i _=> (E' i).le))
end YM.WilsonCoeffUV.Layout
