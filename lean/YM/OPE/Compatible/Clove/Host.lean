import YM.OPE.Compatible.Clove.Specks
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
local notation "Σ(" i ")"=> VC (U i)
local notation "L!"=> solar G d τ
abbrev MuseJ (i:W)(x y: W→L!)(a b:(i:W)→Site (nρ i))(u:Σ(i)) := (U i).EraL ((U i).slot (x i) (a i)*(U i).slot (y i) (b i)) u
lemma gDuty (n:W→Side)(k:ℕ):0≤ gDump n k:=fun i=> (show 0 ≤ ((n i).val:ℝ)⁻¹^k by positivity)
lemma gLow (n:W→Side) (k:ℕ):gDump n k≤ 1:=fun i=> pow_le_one₀ (by change 0 ≤ ((n i).val:ℝ)⁻¹;positivity) (show ((n i).val:ℝ)⁻¹≤1 from inv_le_one_of_one_le₀ (W_le _))
lemma gWorry (n:Side)(w K R p:ℝ)(k:ℕ)(hx:(n.val:ℝ)^k * w≤ K*p*R): w ≤ K*(1*(p*((n.val:ℝ)⁻¹^k))*R):=by rw [one_mul, inv_pow]; have ht:0 < (n.val:ℝ):=Nat.cast_pos.mpr n.pos; rw [show K*(p*((n.val:ℝ)^k)⁻¹*R)= K*p*R/(n.val:ℝ)^k from by simp only [div_eq_mul_inv]; ring]; rw [le_div_iff₀ (by positivity),mul_comm]; exact hx
lemma growStuff (hs:G.Simple)(pW:LocalRatio R)(hx:∀ i,k+44 ≤ τ i)(x y:W→L!) (a b:(i:W)→Site (nρ i))(tV:ℝ)(hp:2≤ tV)(ho:∀ i,Settle (a i) (b i) tV)(S:SlopePrice U k u m₁ w) (jT:Phase): WindZ nρ 0 (glideZ (d+d)) (passM x * passM y*gDump nρ k) (fun i u=> (MuseJ U i x y a b u - MuseIn U i x a u * MuseIn U i y b u).seq jT.val):=by
    obtain ⟨u',hU,hr⟩:= vBranch U S hx x; obtain ⟨v',hV,hR⟩:=vBranch U S hx y; let I:= Script.Tile G P.L; let f(k):=cloudFee u m₁ (4*tV) k; have hh:0≤f:=by intro i; unfold f cloudFee; have he:= zero_le_one.trans (widthCost_ge S.base i); have hz:= S.height; positivity
    obtain ⟨c,hc,H⟩:=marvel (I:=I) jT d d (k+44) k m₁ u f (by omega) S.base S.height hh; let D:=glideZ (d+d); let S':ℝ:=1+Fintype.card (Shade G)*m₁; let K':=c*w^5*u'*v'*S'^D; have hS': S'≥1:=le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) S.height); have htK : S'>0:= zero_lt_one.trans_le hS'; have ht:=S.lo; refine ⟨⟨K',(by unfold K'; positivity),fun i z=>?_⟩,fun i=>?_⟩; swap
    · let Y:=U i; let a:=Y.slot (x i) (a i); let b:=Y.slot (y i) (b i); have hpA:a.B:=blotS Y (x i) _
      have hpB:b.B:=blotS Y (y i) _; have hv: ScriptJ.B ((Y.EraL (a*b))-Y.EraL a*Y.EraL b):=by  have hP:= (ScriptJ.height (Y.poolB pW hpA) (Y.poolB pW hpB)); let p':=Y.EraL (a*b); have hV:p'.B:= Y.poolB pW (ScriptJ.height hpA hpB); exact ScriptJ.Xbond ((hV 0).sub (hP 0)) ((hV 1).sub (hP 1)) ((hV 2).sub (hP 2))
      exact hv _
    let Y:=U i; let X:=Y.x; let Z:=Y.rungS; let V:=mintR Z X R Y.b; let T:=Y.power z; let Ep:=Y.E.rollX z (G:=G)
    have hV':= H (nρ i) _ (Chart.tangent G (Blocx Z P.odd_side Y.tH)) Y.γ (Piax Z G Y.U) (S.vent i).full V T (1/4) Y.campP (a i) (b i) (borFlag Z P.odd_side Y.tH Y.U Y.t Y.ok.1 pW Y.hx _ _ S.base S.height (S.vent i).dot _ hp _ (a i) Y.b Ep) (fun k h=>spiral Z P.odd_side Y.tH Y.U Y.t Y.ok.1 Y.hx S.base S.height (S.vent i).dot k (a i) (b i) hp (ho i)) _ S.lo (S.weights i) _ _ _ _ (hr i) (hR i)
    simp only [care,pow_zero]; simp_rw [Pi.mul_apply]; apply gWorry; simp_rw [show MuseIn U i x a z= _ from gateZ Y pW hs z (a i) (x i), show MuseIn U i y b z=_ from gateZ Y pW hs z (b i) (y i),show MuseJ U i x y a b z= _ from gateL Y pW hs (x i) (y i) (a i) (b i) z]; unfold Mold Shell.grain at hV'; simp only [sub_zero] at hV'; -- schema.F
    apply le_trans (show ( (nρ i).val:ℝ)^k *( _:ℝ) ≤ c*w^5*(u'*‖x i‖)*(v'*‖y i‖)*(1+‖Y.power z‖)^D from hV'); have hd:= plusV' U S i z; apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖Y.power z‖) hd D) (by change 0 ≤ c*w^5*_*_; positivity)); rw [mul_pow]; unfold K' passM S' D; exact le_of_eq (by ac_rfl)
end Scape
end YM.OPE.Quit.PriceZ
