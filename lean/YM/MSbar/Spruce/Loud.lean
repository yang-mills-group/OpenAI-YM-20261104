import YM.MSbar.Spruce.Cranes
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Spruce
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
noncomputable def blastP (p:ℕ) (L:List (Primary c G)) (s:Site f→ G.Color):= blast (poring F ρ) (Rolling.straight F G) (show Matrix (Key F G) (Key F G) ℝ from H⁻¹) (pegged F s (film R T' t p∘ Lodge.Clamp g)) (center F ρ) (hands F G) (ink c l e) (stampD F v G) (barbed F v χ T') L
variable (L':List (Primary c G))(hk:Kind T')(hp:Critical F R.clip R.path ρ) (hd:ClassicalMatch F R.clip l R.path e ρ) (hξ:LocalRatio χ)(hK:(mold R F v).PosDef)(hw:Premier (Rolling.main f R.clip R.path))(he:S.patch.Branches S.kernel G)
local notation "Ω'"=> blastP F R v χ t e l ρ T' g p L' s
local notation "Φ'"=> song F v R.path R.clip χ T' ρ
include hk hp hd hξ hK he hw
lemma fiscal : Lap p (fire (song F v R.path R.clip χ T' ρ) (ink c l e) Z L') (owes (Rolling.straight F G) (show Matrix (Key F G) (Key F G) ℝ from H⁻¹) (barbed F v χ T') (cycleP F v L') (throne F ρ Z) p) :=by -- fiscal yes
     have hb:=well F v χ T' hk; let E' := edgesK F R.path e R.clip l v ρ he hw hp hd hK
     let χ0:= H⁻¹; let D:=α!* (show Matrix (Key F G) (Key F G) ℝ from (mold R F v)⁻¹)* (α!).transpose; let v':=growP a' (cycleP F v L') D (p+1); let A':= τ'; let V':= port (α₀) (song F v R.path R.clip χ T' ρ) L'; have hv:Lap p (PowerSeries.map (Rolling.rail A').toRingHom v') V':=by
           unfold v'; rw [← hand F v χ T' hξ hk]; exact hence A' _ (show Matrix _ _ ℝ from χ0) hK.inv _ _ _ _ _ E' hb L' -- signature
     intro i hi; unfold fire pulseR owes picture; rw [PowerSeries.coeff_map,PowerSeries.coeff_map]; change eval Z (PowerSeries.coeff i V')= _; rw [←hv _ hi,PowerSeries.coeff_map]; rw [show eval Z ((Rolling.rail A').toRingHom _)= eval (A'*ᵥ Z) (PowerSeries.coeff i v') from congr_fun (Rolling.clearL A' Z) (PowerSeries.coeff i v')]; unfold A' poring; rw [LinearMap.toMatrix'_mulVec]; rfl -- 
local notation "γ"=> cup F Z (PowerSeries.coeff 0 (cycleP F v L'))
variable (hF:Canopy (pegged F s (film R T' t p ∘ Lodge.Clamp g)))
include hF
lemma rareW : blastP F R v χ t e l ρ T' g p L' s Z = hint (center F ρ Z) (1:Matrix (Key F G) (Key F G) ℝ) (show Matrix _ _ ℝ from (mold R F v)⁻¹) (pegged F s (film R T' t p ∘ Lodge.Clamp g)) (cup F Z (PowerSeries.coeff 0 (cycleP F v L'))) :=by
     let u':= P!; let C: Matrix P0 P0 ℝ:=H⁻¹; let D':= leeway hF; let Δ':=edgesK F R.path e R.clip l v ρ he hw hp hd hK; have ht:=well F v χ T' hk; let b:=center F ρ; let K:= fun x:Positions P0=> u' (pen (b Z) (1:Matrix P0 P0 ℝ) x); let S' : SpringK (Joint F G):= a'; let G':= cycleP F v L'; let v'(L:List V):=PowerSeries.coeff 0 (readScore ι! b' a' L); let vk(x:Positions P0):=eval (pen (b Z) (1:Matrix P0 P0 ℝ) x) (cup F Z (PowerSeries.coeff 0 G')) -- shadow!!!
     have hT (x:Positions P0):pen (b Z) (1:Matrix P0 P0 ℝ) x=x+center F ρ Z:=by unfold pen b; rw [one_mulVec,add_comm]
     have hx(x:Positions P0): eval (present τ' α! Z x) (v' L')= vk x :=by
          unfold v' vk; rw [valet,Duel.meetE,hT,add_comm _ (center F ρ Z),Duel.hand F _ χ T' hξ hk]
     have hv(x:Positions P0):actor τ' α! u' (center F ρ) (v' L') Z x= K x*vk x :=by unfold actor; rw [hx,mul_comm]; unfold K; rw [hT]
     have hy : (∫ x:Positions P0,K x∂fieldLaw C) = Lodge.shore (fieldLaw C) (center F ρ) (fun x:Positions P0=>x) u' Z:=by unfold K Lodge.shore; simp_rw [hT]
     unfold blastP blast; rw [Duel.wick _ _ C (hK.inv) u' _ Z D' (fun i=>center F ρ (bolt i)) _ _ _ Δ' (fun i=>rfl) S' ht,mark0 τ' α! C hK.inv u' b Z D' _ _ _ _ Δ' (fun i=>rfl) S' ht L'] -- ambiguous vk.OK
     unfold delta drag hint; change (∫ i,actor τ' α! u' (center F ρ) (v' L') Z i∂fieldLaw C)- (∫ i,eval (present τ' α! Z i) (v' L')∂fieldLaw C)* Lodge.shore _ _ _ u' _=(∫ i,K i*vk i∂ fieldLaw C)-(∫ i,K i∂fieldLaw C)*(∫ i,vk i∂fieldLaw C); simp_rw [hv,hx]; rw [hy,mul_comm (Lodge.shore ..)]
end YM.MSbar.Spruce
