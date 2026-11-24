import YM.MSbar.Cypress.BillC
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Cypress
open YM.MSbar.Spruce
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal
open Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Bakery.Film
open Lapaz
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
local notation "A!"=> berth F R v J X Y U' Z t
variable {A B d C P D K w E:ℝ} (h:Suite J χ F X Y (postcard G c t Z) v R (vest (priced F v R.clip R.path) (t • Z)) A B d C P D (linCash F (t •Z)))
variable {a b r D0 d' d0 c' U w' :ℝ} {n p m j N:ℕ}
local notation "α!"=>Rolling.straight F G
local notation "Q'"=> includeX (G:=G) F X
variable (z:Site f)
variable (T':Nesting G f)(g:ℝ→ℝ)(s:Site f→ G.Color)
local notation "P!"=>pegged F s (film R T' t p ∘ Lodge.Clamp g)
local notation "τ'"=> poring F ρ
local notation "φ'"=> center F ρ
local notation "Γ"=> H⁻¹
local notation "Q₀"=> (0:Positions (Key F G))
local notation "c'₁"=> Cacao.growP
local notation "a'"=> barbed F v χ T'
local notation "α₀"=>ink c l e
local notation "b'"=>stampD F v G
local notation "ι!"=> hands F G
open Measuring Ruby UVNext.PricedKernels Laurent Bloch Cane
variable {σ κ :ℕ} {c₁ c₂ c₃ c₄ A0 A' B' K':ℝ}
variable (M:Cross S.ratio.count (TypeFace 1) (TypeFace 1))
local notation "M'"=> installed S.ratio M
variable (h0:Critical F R.clip R.path ρ) (hz:Guessed F (installed S.ratio M) ρ)
local notation "g!"=> crownP F M Z
local notation "f!"=> film R T' t p
local notation "P₀"=>roll S.ratio M G
local notation "P₁"=> (Rolling.stamp F G).comp (center F ρ)
local notation "Φ₁"=> rollW F g!
local notation "Q"=> rollW F s
local notation "V'"=> Primary f G
variable (hS:Parma.Station F v ρ R.path R.clip (installed S.ratio M) n B' c₁ c₂ c₃ c₄) (hb:0 ≤ B') (hx:Cane M A0 A' a E σ κ) -- check
local notation "H!"=> (show Matrix P0 P0 ℝ from (mold R F v)⁻¹)
local notation "µ"=>fieldLaw (show Matrix P0 P0 ℝ from (mold R F v)⁻¹)
-- µ tail condition for δ correction. use inactive row v.F.
variable {k k':ℕ} {b0 σ0 w0 w1 w2:ℝ}
variable (hV: (mold R F v).PosDef)(hc:∀ i:Key F G,(mold R F v)⁻¹ i i ≤ b) -- syntax
open scoped ENNReal NNReal
include hV hc
lemma sparks(k:Primary f G)(hu:0≤ b0)(hp:0 ≤ r) : (fieldLaw (show Matrix P0 P0 ℝ from H⁻¹)).real {x:Positions P0| r < |Rolling.stamp F G x k|} ≤ 2*Real.exp (-(b0*r)+b*b0^2/2):=by
     obtain ⟨⟨j,u⟩,a⟩:=k; obtain ⟨u,rfl⟩:= axisEquiv.surjective u
     simp_rw [show axisEquiv u= coord u from rfl,ruler]; split_ifs with he
     · simp_rw [abs_zero]; simp [not_lt.mpr hp]; positivity
     exact Kelvin.chorus (k:=H!) hV.inv b hc _ r b0 hu
include h0 hz
variable (K_: List (Primary c G)) (i:Primary c G)
local notation "β"=> Lodge.Clamp g
local notation "E₁"=> Lodge.waltz P₀ µ f! (Lodge.Clamp g ∘ (fun y:Positions (Key F G)=> rollW F g! y+ P₁ Z))
variable (hZ: ‖roll S.ratio M G Z‖ +r < w/2)
include hZ
noncomputable def stung (b0 b r:ℝ):= 2*Real.exp (-(b0*r)+b*b0^2/2)
lemma flush (k:Primary f G)(hu:0≤ b0)(hp:0≤ r) : (fieldLaw (show Matrix P0 P0 ℝ from H⁻¹)).real {x:Positions P0| w/2≤ |rollW F (crownP F M Z) x k + P₁ Z k|} ≤ stung b0 b r:=by
    refine le_trans (measureReal_mono (μ:=fieldLaw (show Matrix _ _ ℝ from H⁻¹)) ?_) (sparks F R v hV hc k hu hp)
    intro x hx; change r < _; by_contra! he; change w/2≤ |rollW F g! x k + _| at hx -- edit.Q
    rw [show rollW F (crownP F M Z) x k + P₁ Z k=_ from congr_fun (pose F R Z ρ M h0 hz x) k] at hx; have hp:= abs_add_le (roll S.ratio M G Z k) (Rolling.stamp F G x k); apply not_lt_of_ge hx; exact lt_of_le_of_lt (hp.trans (add_le_add (norm_le_pi_norm (roll S.ratio M G Z) k) he)) hZ
variable (hu:0 ≤ b0)(hp:0 ≤ r)
local notation "α"=> Ω
variable (hg : Lodge.Hat k w w' g) (ht:1 ≤ w') (hh:Lodge.Vase (film R T' t p) k K w) (hw:1≤ w)
variable (hT:Touch R.eval) {F':ℝ → Config G f→ℝ}(hP:Trend F' T' R.path R.clip p) (hf:∀ i ≤ p,Aqua.Stone G i k w0 w1)(h₀ : 1≤ w2)(hτ:w2*t<w0) (hJ:shade G*w≤ w2) (hY:∀ i≤ p, Lodge.Vase (atlas T' p i R.path R.clip) k D w)
variable (ht0 :0<t) (ht':t≤1) (hΘ:K_.length=m) (hσ:m+1 ≤ k)
include hT hP hf hS hb h₀ hτ hJ hY hu hp ht hh hw ht0 ht' hΘ hσ hg
local notation "C'"=> (fieldLaw Γ)
local notation "C₀"=> ((Fintype.card G.ColorIndex:ℝ)*((Fintype.card (TypeFace 1):ℝ)*(c₁+c₁)))
noncomputable def payD (G:Gauge)(c t D w C U:ℝ)(p m:ℕ):= let s:=(Fintype.card G.ColorIndex:ℝ)*((Fintype.card (TypeFace 1):ℝ)*(c+c)); 2^m*s*fCost D t w 0*C + ∑ i∈Finset.range (p+1),t^i*(2^m*s*fCost D t w (p-i)*U)
local notation "sP"=> payD G c₁ t w1 w2 K D p m
lemma effort : |buoy (lightP F R v t ρ T' g (crownP F M Z) p) Z (i::K_)- E₁ (i::K_)|≤ Lodge.boltω m (stung b0 b r) w' K*(c₁+c₂)^(m+1)+(m+1:ℕ)*((c₁+c₂)^m*payD G c₁ t w1 w2 K D p m):=by
     rw [pasture, ←hΘ]; let Mo:= roll S.ratio M G; have hh' :1 ≤ c₁:= (hS.mouth 0 (by simp)).cash;have hK:1≤ c₂:= hS.land.cash; have hc1:0 ≤ c₁:= zero_le_one.trans hh'; have hc2:0 ≤ c₂:= zero_le_one.trans hK
     have hf' := hf _ le_rfl |>.positive; have hK':=hh.pos_; have hD:0≤D:=hY _ le_rfl|>.pos_; have hβ:0≤ K:= hh.pos_
     refine Lodge.flowing P₁ hg hh Φ₁ (continuous_const.add (Rolling.stamp F G).continuous|>.measurable) Z (zero_le_one.trans hw) ht i K_ Mo (flush F R v Z ρ M h0 hz hV hc hZ · hu hp) (by omega) (add_nonneg hc1 hc2) (fun i=>(bud F R v ρ M hS hb i).1.trans (le_add_of_nonneg_left hc1)) (fun i=>(bud F R v ρ M hS hb i).2.trans (le_add_of_nonneg_right hc2)) (by unfold stung; positivity) ?_ ?_ -- order
     · unfold payD; dsimp only; refine add_nonneg ?_ (Finset.sum_nonneg (fun i hi=>?_)) <;> unfold fCost <;> (try clear h) <;> positivity
     intro y hy vk L hE; let A':= aKey F M vk
     have hx := hh.smooth y hy; have hf'' : ContDiffAt ℝ k (Aqua.vine R t) y:=by
          unfold film at hx; have hp := hx.add ((Aqua.pure R T' t p).contDiffAt.of_le le_top); simpa only [Pi.sub_apply,sub_add_cancel] using hp
     have hK:‖tint G _ y‖ ≤ w2:= (tint_le _).trans ((mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hy) (shade_pos _).le).trans hJ);
     have h₂(i:Body 1 f):‖tint G _ y i‖ ≤ w2:=(norm_le_pi_norm _ _).trans hK; have h₁(i:Body 1 f):‖tint G _ (t • y) i‖<w0:=by rw [map_smul,Pi.smul_apply,norm_smul,Real.norm_of_nonneg ht0.le]; exact ((mul_le_mul_of_nonneg_left (h₂ i) ht0.le)).trans_lt (by rwa [mul_comm]); -- trans_eq' maybe
     have ht₁ :∀ i≤ p,∀ v:Primary f G,∀ l:List (Primary f G),l.length≤ K_.length→ |buoy (atlas T' p i R.path R.clip) y (v::l)|≤ D:=fun i hi v l hp=> hY i hi|>.part _ hy (v::l) (by rw [List.length_cons]; omega) (by simp)
     have hσ:= pathC hP hT y A' hf h₁ hf'' (show K_.length+1 ≤ k from (by omega)) ht0 h₂ h₀ ht' D K L hE ht₁ (fun v l hp=>hh.part _ hy (v::l) (by rw [List.length_cons]; omega) (by simp))
     have hA:= bondsK F R v ρ M hS hb vk -- v shadows choice! rename ν'
     rw [show _-_ = grad A' from (by exact poles F R ρ M h0 hz vk), takeG k hx]; rotate_left
     · rw [List.length_map]; omega
     refine hσ.trans (add_le_add ?_ (sum_le_sum (fun i hi=>?_))) <;> unfold fCost <;> gcongr
end YM.MSbar.Cypress
