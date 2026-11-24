import YM.LocalTaylorR2.Sails.Muir
import YM.LocalTaylorR2.Sails.Hyacinth
import YM.LocalTaylorR2.Sails.Orange
import YM.LocalTaylorR2.Marigold.Shipping
import YM.LocalTaylorR2.Sails.Ibis
import YM.LocalTaylorR2.Marigold.Titan
import YM.LocalTaylorR2.Graft1.Bulk
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Marker
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Leaf R) (X:Coat T F) (H:Cash W x μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G}

local notation "i₀" => M.turn.badge S
open Port Charge
open Reserves Tender Gas Ursell Trees Mixed
variable {j k n l : ℕ} {v₀ r d A D x' C' ζ η c' y: ℝ} {χ : Chi} (Ξ:Utopia H j v₀ d r C' χ)
open Candle Daisy.Charity
open scoped Classical
open Tail Blush Next.Foundations Planned.GuardedAtom
open Ovens Extra.Histories Progress.DirectedRecipe YM.Planned
variable {v r B w σ a e s' δ : ℝ}{A':BudgetPoint}{l0 q η : ℝ}
-- apply `Trailer` only to available shape.H.P. Profile at output.Raw value
variable {U ε :ℝ} {δ0:Target.Expense Q}
variable (Ψ:Strange.Engine G) (hg: ReliefBook Ψ Q δ0 L W μ x o A'.order A'.power l Chi.canonical ε U) (hp:0<U)(ht:Stamp T) (hq:A'.supportExponent+2≤ δ0.earn)
    (hb:A'.B=radiusB x)(hx:A'.threshold=Pressure.temp x)
include hg
include hp ht hq hb hx
variable {ψ:Reel.Scroll G f}(X':Cash W x μ L Q o C T (Reel.bend R ψ))
include X'
open Reel (Strand)
lemma coastDeep (M:Leaf R) (z: Site c)(hz:z∈M.crest.image S.ratio.parent) (take:H.fragrances→ ℕ→Prop)(i:ℕ)(hi:i ≤ l+1)(he:∀ u q,take u q→i≤q)(hg0:∀ u q,take u q→ q ≤ l):
    let Y u:= routeP M H u take (Ψ.plug H ψ l) Chi.canonical l
    Coast A' z (locus M H z) Y (markBill M Q*(betaF G x L^requested i (ε/2)/U)) ∧ ((∀ u q,take u q→ q ≤ l)→ Coast A' z (locus M H z) ((fun i=> roadway M H i take ψ Chi.canonical l)-Y) (markBill M Q*(betaF G x L^requested (l+1) ε/U))) :=by
    intro U'
    obtain ⟨A,a',q,d,v,t,r,B,k,D',x',b,y,K,θ,ρ,w,k',n,E₀,z₂,hy,hqB,hS,h⟩:=hg
    obtain ⟨N,hC,hF,hG1,hG,hK,hP₀⟩:= h _ _ S T ht R C H
    obtain ⟨hL,hq',he',hr',hR,hA,hP,hQ,hB,hD,hE,hX,hM,hU,hu,hh,-⟩:= hy; have hj := δ0.first; let Z:= δ0.one/2; have ha: δ0.earn+Z+Z ≤ Q.exp:= by unfold Z; linarith [δ0.worth,δ0.second]
    have h':0 ≤ (l+1:ℝ):= by positivity
    obtain ⟨N',hE',hV',hξ',hh₁,hH,hP₁⟩:= h _ _ S T ht (Reel.bend R ψ) C X'; let ξ:= N'.conduit
    have hK':= (le_add_of_nonneg_right (budget_nonneg (hE'.leases.hit 0))).trans hqB
    let Ω:= Grafting.teen ξ hL h' hE' hK' N hC
    have ha': LocalBookingsR2 (l+1:ℝ) (b+b) Ω.conduit:=Grafting.charters _ _ hL h' hC hE' hK'
    let A'':= Grafting.teen ξ hL h' hE' hqB Ω ha'
    let W:= A''.conduit; have huL:LocalBookingsR2 (l+1:ℝ) (b+b+b) W:= Grafting.charters _ ξ hL h' ha' hE' hqB
    have hW i: ξ.goalsL i+ξ.goalsL i ≤ W.goalsL i:= add_le_add_left (le_add_of_nonneg_left (N.conduit.uses.nonneg (.inr (.inl i)))) _
    have hr := authorizes M H A'' hF hK hL h' hr' hq' huL he' hA (show R.p.B≤_ from (by rw [H.laws.intake.sizes,H.laws.data.funds.length_eq]; exact hP)) hX hM hU (half_pos hj) hR ha hu
    have hv:= papers M H A'' hF hK hL h' hr' hq' huL he' hQ hB hD hE (enlarged1 H Ω.conduit ξ hL h' ha' hE' hqB Ω.balance (enlarged1 H N.conduit ξ hL h' hC hE' hK' N.balance hG))
    have hy: Sailor G A'.threshold k A'.order:= ⟨fun c u h=>N.weigh.stroke c _ (h.trans (hx.trans_le N.talent))⟩
    let d:=markBill M Q; have hd:0≤d:=mul_nonneg (R.p.loMass _ _ M.profit|>.trans' M.profit) (Real.exp_pos _).le; have hY:0< Q.goal L x:=Real.rpow_pos_of_pos (zero_lt_one.trans_le hL) _
    let V i:= Orbit.contourX H ψ Ψ l (Reel.Strand.dial i*ρ^l); let V' f Φ (i:H.fragrances):= routeP M H i f Φ Chi.canonical l
    let R':= Coast (G:=G) A' z (locus M H z) -- H implicit?
    have hP (take:H.fragrances→ℕ→Prop)(hp0:∀ u q,take u q→ q ≤ l) (t':Strand)(i:ℕ)(hi:i ≤ l+1)(he:∀ u q,take u q→ i≤q): R' (V' take (V t')) (markBill M Q*(betaF G x L^requested i (ε/2)/U)):=by
        have hh' := Orbit.ladleX H Chi.canonical A''.conduit Ψ hP₁ (fun i=> (le_add_of_nonneg_right (Tender.logN N'.conduit i)).trans (hW i)) t'
        have hN :AttireD H M (V t') l Chi.canonical A'.order (Price.schemePrice A'' D' x' θ) (fun p=> period M H p A'' x' D' K y θ) (refund M Q L x y) v:= by
           constructor
           · intro i q U hx; unfold cappedB maskSX; split
             · rename_i hq₂; apply lavenderS _ H _ A'' hF hK hq' he' hP₀.positively hP₀.bank hh' _ _ U hx; intro h; rw [h] at hq₂; change l+1 ≤ l at hq₂; omega
             intro E _ _ _ V y he hp; apply Brush.zi (Eventually.of_forall fun _=> rfl) (mul_nonneg (by exact hv.good) (by exact (hv.credit i q).2.1)) zero_le_one
           intro i q U hx; unfold cappedA maskSX; split
           · rename_i hq₂; apply beelineS H _ A'' hF he' hP₀.positively hP₀.bank hh' _ _ U hx; intro h; rw [h] at hq₂; change l+1 ≤ l at hq₂; omega
           intro E _ _ _ V y he hp; apply Brush.zi (Eventually.of_forall fun _=> rfl) (hv.thought.pos _ q) zero_le_one
        constructor
        refine ⟨_,fun u=>conesD (hS:=hh'.love) M H hv u take (V t') hN (hp0 u) hx le_rfl N.income hy N.near N.position z hz i (he u), budget_loosen (aged M H hv hb (half_pos hj) hr z hz hq i) ?_⟩ -- k vs glyph
        let εh:=report G A'.order A'.power Z x w 1 ρ i
        have h : (Q.goal L x*y)⁻¹*εh ≤ (betaF G x L^requested i (ε/2))/U:=(le_div_iff₀ hp).mpr ((mul_comm ..).trans_le (hh i hi))
        apply le_trans _ (mul_le_mul_of_nonneg_left h hd); apply le_of_eq
        change ((d / Q.goal L x)/y * _)*(collars G (δ0.one/2) x A'.order A'.power * (w * (1-1/2)⁻¹))=_ -- RHS h opaque. unfold
        unfold εh Tail.report Z
        simp_rw [one_mul,div_eq_mul_inv,_root_.mul_inv_rev]; unfold d; ring
    
    have hρ:0<ρ:=zero_lt_one.trans_le hr'; let e:ℝ:=(ρ^l)⁻¹; have he':0≤e:=by unfold e; positivity
    let t': Reel.Strand:= ⟨e,⟨by linarith, inv_le_one_of_one_le₀ (one_le_pow₀ hr')⟩⟩
    have hm: Ψ.plug H ψ l=V t':= (Orbit.t'one H Ψ ψ l ρ hρ).symm
    have hM : Reel.sprout H ψ=V Reel.Strand.bud:= (Orbit.t'zero H Ψ ψ l ρ).symm
    change R' (V' take (Ψ.plug H ψ l)) _ ∧ (_ → R' (V' take (Reel.sprout H ψ)-V' take (Ψ.plug H ψ l)) _)
    rw [hm,hM]; refine ⟨hP take hg0 t' i hi he,fun hX=>?_⟩
    let T' i q:= take i q ∧ 1≤ q; let f i:= V' T' (V i)
    let X:=f Reel.Strand.bud-f t'
    rw [show V' take (V Reel.Strand.bud)-V' take (V t')=X from funext fun i=> currencyD M H _ _ _ _ Chi.canonical l]
    let m:ℝ:=betaF G x L^requested (l+1) ε
    apply (Coast.enlarge _ _ _ (Coast.strandsP A' z (locus M H z) f t' (fun p=> hP _ (fun i j h=> hg0 i j h.1) p 1 (by omega) (fun i _ hp=> hp.2)) (fun i Y hh=> orangeD M H i T' V N l (Orbit.flightX H Chi.canonical Ψ hP₁) (fun i' hi'=>hX i _ hi'.1) le_rfl _ hx z Y hh) he')) _
    calc _ = d*((Reel.Strand.spelling l * (ρ^l)⁻¹*betaF G x L^requested 1 (ε/2))/U):= by rw [show markBill M Q=d from rfl, show Reel.Strand.dial t'=(ρ^l)⁻¹ from rfl]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hS hp.le) hd
end YM.LocalTaylorR2.Marker
