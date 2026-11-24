import YM.Juniper.Mulberry.Rarity
/-!
 # Crude physical derivative prices retaining full real Tilt and denominators

 ANY window estimate, uniform all neighbors. No assumptions that flagged pieces analytic.
 Numbers can be ludicrously large in βhat etc, sufficient for thermal
 upgrade because only at limited localization windows. Proofs adapted from
 Token/{Fluent,Purple,Card}. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Mulberry
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Sienna Token Analysis
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f:Side} {S : StepData c f} (F:Forest S.ratio) (T: Tube G S) {r t v u s:ℝ}
    (B : BudgetPoint) (β:ℝ) (O:ChartRatio G) (k:S.Choices) (ρ : Bid.Dir G c→ AxisChart G F)
    {D : ℝ} {j n:ℕ}
local notation "X"=>Positions (Uniform.Primary c G)
local notation "A"=> Pane.virgin T B β
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "M"=> (Fintype.card (Site f):ℝ)
variable (P: Activities G f)
local notation "U*"=> fleece T B β P
local notation "Yu"=> fun x:X=> represent (tint G _ x)
local notation "V'"=> Lapis.orbit F ρ
local notation "p"=> Lapis.table F k T.up T.high
local notation "q"=> Lapis.mist F O T.up
local notation "K"=> Lapis.gram F T.up T.high ρ k
local notation "X₀"=> closedBall (0:Poll.Body (Precision.Key F G)) D
local notation "ε"=> (adjustment F ρ P)
local notation "Ω"=> (Lantern.grace p q V' K + adjustment F ρ P)
local notation "Ω'"=> (gStep β)
variable (h : P.Valid B r v) (hp: title P) {J:Teller G} (ht: Intake J T t (Pane.virgin T B β))
    {c' C Z a Q δ L :ℝ}
local notation "Q'"=> (tempered F T B β P)
local notation "K*"=> (fun x:X=> solar F O β * Real.exp (-coverLog F T O k ρ β x))
local notation "r*"=> cut (sweep (K 0)⁻¹) X₀ Ω
variable (H : Golf (Lapis.table F k T.up T.high) (Lapis.mist F O T.up) (Lapis.orbit F ρ) (Lapis.gram F T.up T.high ρ k) j D u u c')
    {x : Positions (Uniform.Primary c G)} (hx:‖x‖< u)
local notation "b!"=> (crestF T B β P)
local notation "u'"=> Token.prime G S.kernel n Z C β Q
variable (he:0 ≤ Token.prime G S.kernel n Z C β Q)
variable (hC:Fintype.card (Pressure.Bond c) ≤ Q) (hv:PaintSupply G n Z) (hh:Brush n C 1 Real.exp 0)
include hv hC hh
local notation "f*"=> (fun y=> S.density β _ (Yu y)) -- not used
lemma brighter (i:F.Slice G) (hx:‖x‖≤1): Brush n (u' * tempered F T B β P (Yu x) i) 1 (fun x : X=> tempered F T B β P (Yu x) i) x:= by
   have ht:0≤ tiltF B P (F.drape i):= Real.exp_nonneg _
   let Y':= tiltF B P (F.drape i); let T':= fun x:X=> Fare.overall F T B β (Yu x) i
   have hu:= Token.volumeQ F T B β i hv hC x hx hh; have hq:= hu.smul Y'; change Brush _ (_ * (T' x*Y')) _ (fun x=> T' x*Y') x; rw [Real.norm_of_nonneg ht] at hq; rw [← show Y'*(u' * T' x)=u'*(T' x*Y') from (by ring)]
   exact hq.shimmy (Eventually.of_forall fun x=> mul_comm ..)
include H ht h hp he hx
lemma lamp : Brush n (u'* b! x) 1 b! x:= by
   let f(x:X) (i:F.Slice G):= Q' (Yu x) i; have hg y:= fulling F T B β P h hp ht (Yu y)
   obtain ⟨u,hu⟩:= (U*).envelope (show (U*).Lawful J.top.width J.top.paths (ConnectedActivityE6.loopBill G S.patch.L t) r v from ⟨ht.cap.paths,h⟩) |>.cost
   obtain ⟨b,hb⟩:= S.density_bound (ht.ready.knobs.symm ▸ ht.ready.kernel) β
   have hY: ∀ᶠ i in 𝓝 x,‖i‖<1:= continuous_norm.continuousAt.eventually (gt_mem_nhds (hx.trans_le H.small))
   have hM: Meristem f x (F.order G) n:= by
       refine Meristem.points f (F.order G) ⟨fun _=> u'*(|b| * |u|),integrable_const _, hY.mono fun y hy i=>?_⟩ (Eventually.of_forall fun y=> (hg y).1.meas)|>.1 -- absolute
       apply (brighter F T B β P hC hv hh i hy.le).climb _ le_rfl
       apply mul_le_mul_of_nonneg_left _ he; let f':= F.drape i
       rw [tempered,Fare.total]; -- d unfold
       have hy:(A).eval f'* tiltF B P f'=(U*).eval f':=(tilted T B β P hp f').symm; rw [mul_assoc,hy]
       apply mul_le_mul ((hb _ _).trans (le_abs_self _)) ((le_abs_self _).trans ((hu _).trans (le_abs_self _))) ?_ (abs_nonneg _); rw [← hy]; refine mul_nonneg ?_ (Real.exp_pos _).le; rw [Pane.sparkling]; split <;> positivity
   rw [show b! = (fun x=>∫ i,f x i ∂ F.order G) from funext (fun x=>hg x|>.2)]
   exact hM.buds _ (((hg x).1.integrable _).const_mul _) zero_le_one (MeasureTheory.integral_const_mul ..).le (ae_of_all _ fun i=> brighter F T B β P hC hv ‹Brush n C 1 Real.exp 0› i ((hY).self_of_nhds.le))

variable (hd:Brush n a 1 Real.log 1) (hZ : 0<crestF T B β P x)
include hd hZ
lemma spry : Brush n (Lantern.clump n u' a) 1 (fun y=> veilF T B β P y-veilF T B β P x) x:= by -- mirror of Token.lyres
   let f y:=(b! x)⁻¹*b! y; have h :=lamp F T B β O k ρ P h hp ht H hx he hC hv hh; have hz : f x=1:= inv_mul_cancel₀ hZ.ne'; have hf:= h.smul (b! x)⁻¹; rw [Real.norm_of_nonneg (inv_pos.mpr hZ|>.le),mul_left_comm,inv_mul_cancel₀ hZ.ne',mul_one] at hf; refine (composite hf (show Brush n a 1 Real.log (f x) from hz ▸ hd)).shimmy ?_
   filter_upwards [h.smooth.continuousAt.eventually (lt_mem_nhds hZ)] with y hy; change Real.log (b! y)-Real.log (b! x)=Real.log (f y); unfold f; rw [Real.log_mul (inv_pos.mpr hZ|>.ne') hy.ne',Real.log_inv]; ring

local notation "f"=> lacking F T B β O k ρ P D -- conflicts f side notation rm near?
local notation "b*"=> (q) -- unused
local notation "Z*"=> Token.oat n c' β
lemma sponsor (hj:n≤j)(hh' : Brush n δ 1 (Mulberry.cutLog F T β O k ρ P D) x) (hy: |(lacking F T B β O k ρ P D x)| ≤ L) : Brush n (Lantern.clump n u' a+(Z* + Z*)+ (δ+δ)+L) 1 (f) x:= by
   let Z':= cutLog F T β O k ρ P D; have hp' := hh'.separating ((Brush.certified zero_le_one _).climb hh'.bound le_rfl)
   apply ((((spry F T B β O k ρ P h hp ht H hx he hC hv hh hd hZ).gathering (Token.octane F T O ρ β k hj hx H ht.positive)).separating hp').gathering ((Brush.certified zero_le_one _).climb hy le_rfl)).shimmy; apply Eventually.of_forall; intro y; unfold lacking; ring_nf
end YM.Juniper.Mulberry
