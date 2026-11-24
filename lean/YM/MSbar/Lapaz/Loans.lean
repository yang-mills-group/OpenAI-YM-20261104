import YM.MSbar.Lapaz.Utopia
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Lapaz
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal
open Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Bakery.Film
variable {G:Gauge}{c f:Side} {S:StepData c f}(F:Forest S.ratio)(R:Rep G f)(v:S.Choices)(J:Voice G)(Q:Palisade)(χ:ChartRatio G)
local notation "V"=>Primary c G
local notation "P0"=>Key F G
local notation "G!"=>Joint F G
local notation "T"=>Positions (Joint F G)
local notation "x!"=> Positions (Primary c G)
local notation "Ω"=> address F G
local notation "H"=>mold R F v
variable (X Y:Support f)(U':Config G f) (t:ℝ)(Z:Positions (Primary c G))
local notation "Λ"=> includeX (G:=G) F X
local notation "X₀"=>SpaceP F X G
local notation "χ!"=>(pinch (includeX (G:=G) F X) H)⁻¹
variable (e:PathData G)(l:Clip)(ρ:fieldDir G c 1→ AxisChart G F)
local notation "ν"=>vest (priced F v R.clip R.path) (t • Z)
local notation "f1"=>linCash F (t • Z)
open Next.SectorChange
local notation "I!"=>hotel F X Y J (postcard G c t Z) (vest (priced F v R.clip R.path) (t • Z))
local notation "r₀"=>rental F J R Y v (postcard G c t Z) (vest (priced F v R.clip R.path) (t • Z))
local notation "c!"=> sampleY F R v J X Y U' (t • Z)
local notation "µ"=> c! ∘ includeX (G:=G) F X
local notation "A!"=> berth F R v J X Y U' Z t
variable {A B d C P D K w E:ℝ} (h:Suite J χ F X Y (postcard G c t Z) v R (vest (priced F v R.clip R.path) (t • Z)) A B d C P D (linCash F (t •Z)))
local notation "S!"=> clipM F X Y (I! A B) χ t (c! ∘ includeX F X) U'
local notation "D!"=> Bakery.Film.draw F X U' (c! ∘ includeX F X) t
local notation "F!"=> fun z:SpaceP F X G=> fLog F X χ t z (c!∘ includeX F X) U' r₀ (show Matrix (Lake F X G) (Lake F X G) ℝ from (pinch (includeX F X) H)⁻¹)
variable (ht:0<t)(u x:SpaceP F X G)
include ht
local notation "Q₀"=> chambers F Y J (postcard G c t Z) ν
local notation "W"=> postcard G c t Z
variable (hU:U'∈ hotel F X Y J (postcard G c t Z) (vest (priced F v R.clip R.path) (t • Z)) A B)
include h hU
local notation "L!"=> fun z:X₀=> meetVar Z (A! z)
local notation "P!"=> fun z:X₀=> stamp F G (A! z)
local notation "θ"=> swung F χ
local notation "φ"=> pushChart F G v
variable (H':Nesting G f) (p:ℕ)
variable (L:List (Primary c G))
variable (A':Ages)
local notation "A₀"=> meetVar Z (A! 0)
local notation "Q'"=>barbed F v χ H'
local notation "χ₀"=> cycleP F v L
local notation "X!"=>vene X F G
-- Budget only sensor.
local notation "F₀"=> Set.indicator (I! A B) (rave S (t⁻¹^2) t R L Z)
variable {n m N k σ b s0 : ℕ} (a:ℝ) (x0:Site f) (hv: Posture Q J F A B K w n m X Y (t • Z) (vest (priced F v R.clip R.path) (t•Z)) R.p) (hS:Ages.Vying A' p s0 t H' F R χ v) {Tx U V1:ℝ}
variable (hp:Picked G S F w)(hX:∀ i∈ L, S.ratio.embed (Measuring.chart c G i)∈X)
variable {τ D' E' K' H₁:ℝ}(hR:R.Lawful τ D' E' K' H₁)(hT: ∀ i,0<R.eval i) (hh:t ≤1) (hχ:LocalRatio χ)(hg:Clear G J)(hK:S.patch.Branches S.kernel G)
local notation "B₀"=> hotel F X Y J W ν A B
include hp hT hv hX hR hS hh hχ hg hK
variable (ha:0 ≤ a)(hQ:∀ i≤p, Tokew (address F G) a k (σ+b) 0 (PowerSeries.coeff i (singularity (pushChart F G v) 2)) Tx)(hd:ranged F L x0 N) (hf:p+2 ≤ σ)(hx:L.length≤ b)(hw:b*(p+2) ≤ σ)
noncomputable def Bmark (G:Gauge)(m k p b M:ℕ) (x: Site f)(v w a:ℝ) := barry 0 m p ((plateD x a p k m b M v)^b) w
noncomputable def Emark (A':Ages) (s w t:ℝ)(m r p:ℕ):= t^(p+1)*(spoolP s w (A'.k1*A'.outer^(p+3)) m)^r
local notation "W'"=>A'.outer
local notation "T0"=> Bmark G σ k p b N x0 Tx W' a
local notation "U₀"=> barry 0 σ p ((liftW a k N)*Tx) W'
local notation "D₀"=>Emark A' T0 U₀ t b L.length p
include ha hQ hd hf hx hw
set_option maxHeartbeats 500000 in
lemma honorM (ho:1 ≤ A'.outer)(he:L.length ≤ s0)(hr:∀ i:SpaceP F X G,i∈ S! → ‖meetVar Z (A! i)‖ ≤ A'.outer):
   (∀ i:SpaceP F X G,i∈ S! → |(F₀ (D! i)) - taste p (picture (meetVar Z (A! i)) (cycleP F v L)) t| ≤ Emark A' T0 U₀ t b L.length p ) ∧
   ∀ x:SpaceP F X G, Belt p (micro (meetVar Z (A! 0)) (vene X F G) (cycleP F v L) x) ≤ Bmark G σ k p b N x0 Tx W' a*(1+‖x‖)^(σ+2):=by
   let f₀:=F₀; have h: Vows G R H' χ F v p s0 t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _:=hS -- annotate
   constructor
   · intro v' hv'; rw [Set.indicator_of_mem (show D! v'∈ I! A B from hv'.1), Tonic.equity (t⁻¹^2) t v Z L hK R τ D' E' K' H₁ hR hT F X Y J Q ν hg hv hX hp (D! v') hv'.1];
     have hk: Q₀ (D! v')=parmaM F (A! v') t:=by rw [Jade.applies F R v J χ X Y U' t Z ‹Suite ..› ht v' hU hv']; unfold parmaM; rw [←Parma.dresses]; unfold postcard; rw [map_smul,map_smul];rfl -- fix via Works.tang
     rw [hk]; have h₀:1≤ A'.outer:=ho -- not guaranteed! add requirement. supply
     refine Bout.sail F v Z (A! v') L p x0 hQ hd ha ht hh ((show ‖t•(meetVar Z (A! v'))‖≤ t*A'.outer from ?_).trans_lt h.hp3) (hr v' hv') h₀ hK h.shape h.rank hw le_rfl hx hf he
     rw [norm_smul,Real.norm_of_nonneg ht.le]; exact mul_le_mul_of_nonneg_left (hr v' hv') ht.le
   intro i; have hw':0≤ Tx:=(hQ _ le_rfl).1; refine baro (y':=k) F R v J X Y U' t Z i p (cycleP F v L) σ x0 a ?_ (hr 0 (born F R v J χ X Y U' t Z (by assumption) ht hU)) ha
   intro i hi; obtain ⟨he,hv'⟩:= Bout.hearts F v L p x0 hQ hd ha rfl hx (show σ+b ≤ σ+b from le_rfl) i hi; exact ⟨Quote.widen he (pow_le_pow_right₀ (le_add_of_nonneg_right (by have hw:=wpos a k N; positivity)) hx) le_rfl,hv'.trans ((Nat.mul_le_mul_right _ hx).trans hw)⟩
end YM.MSbar.Lapaz
