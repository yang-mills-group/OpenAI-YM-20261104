import YM.OPE.Compatible.Clove.Realm
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.PriceZ
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
namespace Scape
variable {W:Type}{nρ fρ:W→Side}(U:(x:W)→ Scape K T P (nρ x) (fρ x) i j R) {u m₁ m₂ m₃ w:ℝ}{q:W→ℝ}{s:ℕ}
structure SlopePrice (k:ℕ)(u c b:ℝ):Prop where
    base : 0 < u
    height : 0≤c
    vent (x:W): Telet P (U x).U u c
    lo : 1 ≤ b
    weights (x:W): weightsB (mintR (U x).rungS (U x).x R (U x).b) (k+44) (fun _=>b)
    flight (x:W):
        let Y:=U x; soot (k+24) (voteV P K.K Y.x.live Y.x.clip 3) b ∧ soot (k+24) (voteV P K.K Y.x.live Y.x.clip 4) b ∧ soot (k+24) (Y.U.Fly Y.x.live Y.x.clip) b
local notation "Ξ" i=> VC (U i)
local notation "Y!"=>solar G d τ
lemma L_norm (S:SlopePrice U k u m₁ w)(j:W)(p: Ξ j): ‖(U j).power p‖≤ Fintype.card (Shade G)*m₁*‖p‖:=by
     let y:=U j; let Y:=rayS _ y.E G p
     rw [show (U j).power p=_ from bounty y.rungS P.odd_side y.U y.t y.ok.1 Y]; refine (vape u m₁ y.U.main (S.vent j).main S.base.le S.height _).trans (mul_le_mul_of_nonneg_left (ray_norm _ _ _) (mul_nonneg (Nat.cast_nonneg _) S.height))
lemma plusV' (S:SlopePrice U k u m₁ w)(j:W)(p: Ξ j):1+‖(U j).power p‖ ≤(1+Fintype.card (Shade G)*m₁)*(1+‖p‖):=by have he:=L_norm U S j p; have hv:0≤ (Fintype.card (Shade G):ℝ)*m₁:=mul_nonneg (Nat.cast_nonneg _) S.height; nlinarith [norm_nonneg p]
abbrev gDump (X: W→Side)(k:ℕ):W→ℝ:=fun i=>((X i).val:ℝ)⁻¹^k
def passM (p:W→Y!):W→ℝ:=fun i=>‖p i‖
abbrev MuseIn (i:W)(p:W→Y!) (a:(i:W)→Site (nρ i))(y: Ξ i):=(U i).EraL ((U i).slot (p i) (a i)) y
abbrev MuseOut (i:W)(p:W→Y!)(a:(i:W)→ Site (nρ i))(hs:G.Simple)(hr:LocalRatio R)(h:Aware d τ)(y: Ξ i):=
    let x:=U i
    Stand.charted x.E (cutφ _ ((x.upL hs hr h (p i)).val) (a i)) y
lemma vBranch (_S:SlopePrice U k u m₁ w)(ht:∀ i, k+44 ≤ τ i)(p:W→ Y!):∃ c:ℝ,0≤c∧∀ i:W,Tide (branchOut P G (spread G d τ (p i).val)) d (k+44) (c*‖p i‖):=by
    obtain ⟨a,b,ha,H⟩:= drip_cash G P.L; let T:=costD (Script.Tile G P.L) (size (0:Cover)) (k+44) b a (d+2); refine ⟨T,costD0 ..,fun i=>?_⟩; rw [mul_comm]; exact rebound _ 0 _ a b _ _ _ H ha (resin _ ht)
lemma gU {i:W}(c:ℝ)(hc:2≤c)(S:SlopePrice U k u m₁ w):
     let f:= fun k:ℕ=> cloudFee u m₁ (4*c) k
     let B:= U i; 0≤f∧(Piax B.rungS G B.U).strip u m₁:=by
       intro f B; refine ⟨fun x=>?_ ,?_⟩; unfold f cloudFee; have hh:= zero_le_one.trans (widthCost_ge S.base x); have hv:=S.height; positivity
       exact (S.vent i).full
lemma rampOne (S:SlopePrice U k u m₁ w)(hs:G.Simple)(hr:LocalRatio R)(ht:Aware d τ)(hx:∀ i,k+44 ≤ τ i)(p:W→Y!)(a:(i:W)→Site (nρ i)):
     ∃ c≥0,∀ i y (j:Phase), Mold ((MuseIn U i p a y).seq j.val) ((MuseOut U i p a hs hr ht y).seq j.val) (c*‖p i‖*(1+‖y‖)^glideZ d) (nρ i) k:=by
       let C :=fun k:ℕ=>cloudFee u m₁ (4*(2:ℝ)) k; obtain ⟨z,hz,H⟩:= vBranch U S hx p; have hc:0≤C:=by
            intro j; unfold C cloudFee;have h:= zero_le_one.trans (widthCost_ge S.base j);have ht:=S.height; positivity
       obtain ⟨x,hx',hc⟩:= prisms (I:=Script.Tile G P.L) d (k+44) k u m₁ C S.base S.height hc le_rfl; let T:=Fintype.card (Shade G); let Z:=glideZ d; let v:=x*w^5*z*(1+T*m₁)^Z; refine ⟨v,(by unfold v; have he:= S.height; have hx:=S.lo; positivity),?_⟩
       intro l y j; let Y:=U l; let V:= (Y.rungS); let T':= (Piax V G Y.U); let p':= (spread G d τ (p l).val); let P':= (Y.E).rollX y; let X:= Y.power y; let A:= mintR V Y.x R Y.b; let W:=branchOut P G p'; let b:=Y.b; let R₀:= hc (nρ l) _ (Chart.tangent G (Blocx V P.odd_side Y.tH)) Y.γ T' (S.vent l).full A (1/4) X Y.campP (a l) (borFlag V P.odd_side Y.tH Y.U Y.t Y.ok.1 hr Y.hx _ _ S.base S.height (S.vent l).dot 2 le_rfl (k+44) (a l) Y.b P') w S.lo (S.weights l) _ _ (H l)
       let B':= Mouth T' A W d
       have hf:Tide B' d (k+44) (x*w^5*(z*‖p l‖)):=R₀.1
       let T2:= ((Y.upL hs hr ht (p l)).val); let o:= rayS Y.tH Y.E G y
       have ht' : MuseOut U _ p a hs hr ht y=Libra.Char.go B' d X (a l):=by
            change inkM (Drift.spread G d τ (actor Y.x Y.U R Y.b _ ht (p l).val)) d _ o=_
            have hi:Tide (rushS P K.K Y.x Y.b Y.U R p' d) d (k+44) (x*w^5*(z*‖p l‖) * costD (Shade G) (size (0:Cover)) (k+44) m₁ u (d+2)):= rebound _ 0 B' u m₁ _ _ _ (S.vent l).marr S.base hf
            rw [offered, bustDD P K.K Y.U Y.x R p' _ Y.b (a l) hi]
            · unfold inkM; erw [show X=_ from bounty V P.odd_side Y.U Y.t Y.ok.1 o]; exact sameSide _ _ _ P B' (fun i j=> sootS ((hf i).2 _)) _ _ Y.U.rocket2
       rw [ht',show _= _ from (show MuseIn U l p a y= _ from gateZ Y hr hs y ..)]; apply (R₀.2 j).trans; have he:= plusV' U S l y; apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0 ≤ 1+‖X‖ by positivity) he Z) (by change 0 ≤ x*w^5*_; have he:=S.lo; positivity)); rw [mul_pow]; unfold v T Z; exact le_of_eq (by ac_rfl)
end Scape
end YM.OPE.Quit.PriceZ
