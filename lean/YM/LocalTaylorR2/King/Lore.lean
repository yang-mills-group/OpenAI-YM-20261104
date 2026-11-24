import YM.LocalTaylorR2.King.Account
import YM.LocalTaylorR2.King.Quits
/-! # ALL-field factored density with Iterated E-surplus -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.King
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Ovens Time UVNext UVNext.CouplingReset Daisy.Charity.RG12 Tail
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open CalendarStep
local notation "❖" => Chi.canonical

/-! # Lens core E-error post the actual regroup, with inherited error as input. -/
open Reel Strand Rain Roost Mallow Capstone
variable {G:Gauge}{M:Metals G}{D:Rolls M.p}{A:Alloy M D}
   (Ξ:Engine G) (R:Factor A){m n N:ℕ}{l k:ℝ}{Q:In A.B.a m n}(H:Spring R N m n l k Q) (x:ℝ)(hx:x∈Set.Icc l k)
   (w: Reel.Scroll G (A.B.a.S.side (m+1) n))(p:ℕ)
local notation "z"=> A.B.a.clock.hatBeta m
local notation "z'"=> A.B.a.clock.hatBeta (m+1)
local notation "Ω"=> A.B.a.clock.J (m+1)
local notation "B"=> A.B.a.budget m
local notation "K"=> A.B.a.params m
local notation "b"=> A.B.a.S.side m n
local notation "τ"=> (H.H.latch x)
local notation "d"=> H.ordinal
local notation "I"=> H.H.base
local notation "a!"=> H.V' x
local notation "O"=> H.X'
local notation "r"=> (H.result x)
local notation "xH"=> (Q x)
local notation "γ"=> A.B.kin.alpha N m
local notation "T"=> (A.B.kin.path N m)
local notation "X"=> (H.H.sister (H.H.latch x))
local notation "k₀"=> Rain.lint R.target A m
local notation "a"=> Trio.base k₀ (radiusB z)
local notation "Φ"=> A.B.a.clock.allowance m
local notation "Φ'"=> A.B.a.clock.allowance (m+1)
set_option quotPrecheck false
local notation "w'"=> ((Q (τ)).activities.E)
variable (hE:Mallow.RG12.Earned (ticketD G) R.shape A.delay)(he:Mallow.RG12.Earned (wheelD G) R.shape A.delay)(hΞ:Mallow.RG12.Earned (survey Ξ.toRegime) R.shape A.delay)(hm:m<N)
   (hV:p ≤ A.B.a.clock.J (m+1)) (h₀: 3 ≤ p) {v:ℝ}(hA:Affords (Q x) A.B.a (m+1) w v) (hG:G.Simple)(hk:Mallow.RG12.Earned (overD G) R.shape A.delay) (ε:ℝ) (hP: 3*CalendarStep.loss (A.B.a.clock.J (m+1)) ≤ ε)
local notation "P" => ordersDue Ξ R H x w p
local notation "f" => alumni Ξ R H x w p
local notation "L" => CalendarStep.loss Ω
local notation "fc"=> Time.forecastE A.B.a m
local notation "Ks"=>Time.forecastK A.B.a m R.scout (Q x).beta
local notation "e" => (Capstone.fare k₀ (A.B.a.params m) z+2) * (z' ^ requested (p+1) (L))
local notation "q"=> (2*v/Φ')
local notation "v'!"=> (e+q*fc)
local notation "o"=> (z' ^ requested (p+1) ε)
local notation "p'"=> (o+v/8)
local notation "P₀"=> Time.fraction A.B.a m

def forest := carver T O f γ B (K).clip
def betaEast := predictor A.B N Q x + Averaging.delta ((O).read (f))
def priceNow := Collection.vac f (H.τ x)
local notation "Ū"=> (forest Ξ R H x w p)
-- `rental` stage. You may pay θ conversions. Need not hide h.Core on v valid
structure Inland (key:ℝ) : Prop where
  estate : Sizing A.B.a m (bend (r) ((r).activities.E-Ū)) key ∧ Sizing A.B.a m (bend (r) Ū) (P₀+key)
  stakes (g:ℝ): Sizing A.B.a m (bend (r) ((r).activities.E+g • (Ū-(r).activities.E))) (P₀+ |g| * key)
  price : (r).eval=(bend (r) Ū).eval* fun V'=>Real.exp (-((bend (r) ((r).activities.E-Ū)).activities.additive B V'))
  rooms : HasSlots B (r).activities→ HasSlots B (bend (r) ((r).activities.E-Ū)).activities∧ HasSlots B (bend (r) Ū).activities
  scalar : |(r).v-priceNow Ξ R H x w p| ≤ key
  beta : (B).threshold^2 * |(r).beta-betaEast Ξ R H x w p| ≤ key

include hΞ hE he hk hm hV h₀ hP hx hA hG
omit hm hx hΞ hE hG in
lemma licgate : Time.base G (K)* v'! ≤ p' ∧ v'! ≤ p':=by
   have hC:SupplyF G (D.L Ω) k₀ (K) z (L) :=by rw [params_eq A.B.valid]; exact hk _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)
   obtain ⟨⟨hv,hp⟩,_⟩:= capping (D.L Ω) k₀ (K) z ε B L hC ⟨rfl,rfl,rfl⟩ (by rw [← beta_eq A.B.valid]; exact (A.B.a.fits.delayed _).le) hP p -- beta
   rw [← beta_eq A.B.valid] at hv hp
   rw [Time.table G K ⟨rfl,rfl,rfl⟩] at hp; simp only [abs_zero,zero_mul,mul_zero,add_zero] at hp
   let t:= Time.base G K; let f₀:= q*fc; let E:= e; let y:= Φ'; have he₂:0<v:=hA.leftB
   have hp':0< Φ':= (mul_pos zero_lt_two he₂).trans_le hA.small
   have hq:0<q:=by positivity
   have hl: Φ ≤ 4*Φ':= (Reel.trust _ he _ hV h₀).1
   let C':=Time.credit G K; have hPhi:0≤ Φ:= allow_pos ..
   have hU (b':ℝ) (he:b'*C' ≤ (64:ℝ)⁻¹) : b'*f₀ ≤ v / 8:=by
      calc
       b'*f₀ = q*((b'*C')*Φ):=by unfold f₀ forecastE C'; ring
       _ ≤ q * ((64:ℝ)⁻¹*(4*Φ')):= by
          apply mul_le_mul_of_nonneg_left _ hq.le; exact (mul_le_mul_of_nonneg_right he hPhi).trans (mul_le_mul_of_nonneg_left hl (by norm_num))
       _ = v/8:= by field_simp; ring
   have hbo := Time.authorized G K; have hb:= hU (1:ℝ) (by rw [one_mul]; exact hbo.1); rw [one_mul] at hb
   rw [mul_add]; exact ⟨add_le_add hp (hU t hbo.2),add_le_add hv hb⟩
open Recoil
lemma leaseArg : Inland Ξ R H x w p p':= by
   let B':= (O).read; let D₀:= Collection.shelves O T B
   have ht:=H.core hm x hx; have hT:= H.owns hG hm hx; have hF:= R.machine.passes hm H.knows|>.1
   let V:= ordersDue Ξ R H x w p
   let Z:=H.result x; let Y:= (a!)
   have hh: (P).logRead=(a!).logRead-(f).logRead:= rfl -- syntax notation
   have hX:= arrangement Ξ R H x w p; have hf:=hX.2
   have hu:= rentU Ξ R H x hx w p hE he hm hΞ hV h₀ hA; let U:= (f)
   have hp:Collection.Local O B U (fc+ v'!) Ks:= by
       apply Reel.scoop I (a) (2*a) (B) ht (show U.hardRead=Y.hardRead from rfl) hX.1
       rw [show U.logRead=(a!).logRead-V.logRead from by change _=_-((a!).logRead-_); abel]; exact Reel.gauges_sub (budget_of_local ht) (budget_of_local hu)
   let X':= branch O T (K).clip B; let X₀:= X' (a!) γ
   have hel:=(R.machine.passes hm H.knows|>.1.fees _ hx).regular; let β:= (Q x).beta
   have he₀ (U:Collection.Source G (b))(e' g:ℝ) (h: Collection.Local O B U e' Ks)(j:ℝ)(he: regularNeed G B (K).clip (K).width (K).paths g e' ≤ j): (D₀.pours (X' U g)).Valid B j Ks:=
     (Recoil.enlarge (Recoil.stamp h hG (A.B.support.cap N m hm.le) hF.decent hF.width (Return.enough_room ..) (Q x|>.beta) (H.τ x) g) he le_rfl le_rfl).covers.labels
   obtain ⟨hl,hb⟩:= licgate R x w p he hV h₀ hA hk ε hP 
   have heq: (a!).logRead=U.logRead+(P).logRead:= by rw [hh]; abel
   have hK:= Recoil.painted (W:=T) (c:=(K).clip) ht hG γ hp heq (Eq.refl Y.hardRead) (Eq.refl Y.hardRead)
   have hrE: (r).activities.E=Ū+carver T O P 0 B (K).clip:= by
      rw [annuity hT]; exact Capstone.pouring_reg _ _ hK.reg
   let C₁:= p'; let P':= γ
   have hr:(r).Lawful (K).width (K).paths (A.B.a.clock.loopCap m) Φ (A.B.a.clock.forcedAllowance m) := ((H.moves hG hm).2 x hx).1.bundle.valid
   have hj (t:ℝ)(k':ℝ)(ht:k' ≤ |t| * v'!): regularNeed G B (K).clip (K).width (K).paths γ (fc+k')≤ P₀ + |t| * C₁:= by
       rw [Time.table G K ⟨rfl,rfl,rfl⟩]; rw [Time.table G K ⟨rfl,rfl,rfl⟩] at hel
       have ht := mul_le_mul_of_nonneg_left ht (Time.base_nonneg G K).1; unfold C₁; nlinarith only [ht,hel,mul_le_mul_of_nonneg_left hl (abs_nonneg t)]
   have hy:Sizing A.B.a m (bend (r) Ū) (P₀+C₁):= by
      refine ticket D₀ (y:=X' U γ) hT hr (he₀ U _ _ hp _ ?_); simpa using! hj 1 (v'!) (by simp)
   let x':=carver T O V 0 B (K).clip
   have hz:Sizing A.B.a m (bend (r) x') C₁:=ticket D₀ (y:= X' V 0) hT hr (he₀ V _ _ hu _ (by rw [Time.table G K ⟨rfl,rfl,rfl⟩]; simpa using hl))
   have hΔ:(r).activities.E-Ū=x':=countQ hrE
   refine ⟨⟨hΔ.symm ▸ hz,hy⟩, fun g=>?_,?_,fun h₀'=>?_,?_,?_⟩
   · let Z₀:={(a!) with logRead:= (a!).logRead-g • V.logRead}; let Y':= X' Z₀ γ
     have hk'':Collection.Local O B Z₀ (fc+ |g| * v'!) Ks:= scoop I (a) (2*a) (B) ht rfl (active_sub I hX.2 (active_scale I (active_sub I hX.2 hX.1) g)) (gauges_sub (budget_of_local ht) (gauges_scale (budget_of_local hu) g))
     have hw₀' : Z.activities.E+g • (Ū-Z.activities.E)=drawn D₀ Y':=by
        have hh : Ū-Z.activities.E=-x':=by rw [← hΔ]; abel
        rw [hh,smul_neg, ←sub_eq_add_neg, annuity hT]; exact (carverSub T g ht hu (x:=Z₀) rfl rfl hk'' rfl hG).symm
     show Sizing A.B.a m (bend _ (Z.activities.E+g • _)) _; rw [hw₀']; exact ticket D₀ hT hr (he₀ Z₀ _ _ hk'' _ (hj _ _ le_rfl))
   · rw [hΔ]; exact calculate D₀ hT hy hz hK.reg
   · rw [hΔ]; exact ⟨Capstone.seats_era D₀ (X' V 0) _ h₀',Capstone.seats_era D₀ (X' U γ) _ h₀'⟩
   · rw [H.moves hG hm|>.2 x hx|>.2.2.2]; unfold priceNow; rw [CalendarStep.scalarFee hG hp hu heq (H.τ x)]; exact (CalendarStep.vac_ledger hG hu).trans hb
   unfold betaEast; rw [show Z.beta=predictor A.B N Q x+Averaging.delta (B' Y) from Eq.trans (congr_arg RG.Rep.beta hT) rfl]; rw [add_sub_add_left_eq_sub,CalendarStep.kineticFee hG ht hp heq]; exact (Averaging.delta_bound hG hu.projects).trans hb
end YM.LocalTaylorR2.King
