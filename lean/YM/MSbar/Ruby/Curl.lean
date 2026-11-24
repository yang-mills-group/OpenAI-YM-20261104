import YM.MSbar.Ruby.ViewY
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Ruby
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
open Measuring Cane Laurent Bloch UVNext.PricedKernels
local notation "t₁"=> (S.ratio.count.val:ℝ)
variable (M:Cross S.ratio.count (TypeFace 1) (TypeFace 1)) (O:Ages)
local notation "M'"=>installed S.ratio M
variable (hp:Critical F R.clip R.path ρ)(hz: Guessed F (installed S.ratio M) ρ)(ha:ClassicalMatch F R.clip l R.path e ρ) (hK:Premier (Rolling.main f R.clip R.path))
local notation "g"=>center F ρ
-- orientation field fixed.Re.Row pre.
omit hU h ht in
lemma stun (i:Positions (Key F G)) : ‖stamp F G i‖ ≤ ‖i‖:=by
    refine pi_norm_le_iff_of_nonneg (norm_nonneg _)|>.mpr fun v=>?_ ; obtain ⟨⟨x,b⟩,v⟩:=v; obtain ⟨b,rfl⟩:= axisEquiv.surjective b; change ‖stamp F G i ((x,Exterior.coord b),v)‖ ≤ _; rw [ruler]; split; rw [norm_zero]; exact norm_nonneg _; exact norm_le_pi_norm i _
variable (hG:Clear G J)(hc:S.patch.Branches S.kernel G)(hX:X ⊆ Y)
include hp hU h ht hK hG hc hX
lemma localB (he:x∈ S!) :‖berth F R v J X Y U' Z t x-center F ρ Z‖ ≤ (P+B)/t:=by
     let U₀:= imageNear J F; have hx:= Bakery.Film.shore J F X Y W ν χ hG (linCash F (t • Z)) h.seat hX (D! x) (show D! x∈ I! A B from he.1); have hZ:=lovely F v R.path R.clip ρ hc hK hp (t•Z) h.positivity; rw [map_smul] at hZ
     rw [le_div_iff₀ ht, mul_comm (_:ℝ) t]; nth_rw 1 [← Real.norm_of_nonneg ht.le] -- changes everything. replace
     rw [← norm_smul,smul_sub,hZ]; rw [(sweet F R v J χ X Y U' t Z h ht x hU he).1] at hx; exact hx
variable {C' B' D' V' W' ι α η δ z0:ℝ} {s k j:ℕ}
variable (hq:Cane M C' D' α E k s)(he:0 ≤ η)(hs:Parma.Station F v ρ R.path R.clip (installed S.ratio M) s η ι B' V' W')
local notation "Φ"=> value α C' D' E s k
local notation "s!"=> crownP F M Z
variable (ho:‖Z‖ ≤ z0)
include hs hz he hq ho
omit hp hz hq hU h ht hK hG hc hX in
lemma tends (i:Body 1 f): ‖Wave.ran (crownP F M Z) i‖ ≤ shade G*(ι*z0):=by
     let c:= shade G* (ι*z0); have hh:= ornament F R v Z ρ M he hs; have hz:1 ≤ ι:=(hs.mouth 0 (by simp)).cash; have hh: ‖s!‖ ≤ c:=hh.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ho (zero_le_one.trans hz)) (shade_pos G|>.le))
     exact max_le ((norm_le_pi_norm (s!) _).trans hh) ((norm_le_pi_norm (s!) _).trans hh)
local notation "σ"=> (P+B)/t
omit hz hq in
lemma whirl (hy:x∈ S!) : ‖berth F R v J X Y U' Z t x‖ ≤ B'*z0+(P+B)/t:=by
    have hh :‖center F ρ Z‖ ≤ B'*z0:=(lotus F R v Z ρ M he hs).trans (mul_le_mul_of_nonneg_left ho (zero_le_one.trans hs.land.cash))
    let x':=A! x; let w':=g Z; have hx:‖x'-w'‖ ≤ (P+B)/t:=localB F R v J χ X Y U' t Z ρ h ht x hU hp hK hG hc hX hy -- order
    rw [show ‖A! x‖=‖x'-w'+w'‖ from congr_arg norm (sub_add_cancel x' w').symm]; exact (norm_add_le ..).trans ((add_le_add hx hh).trans_eq (add_comm ..))
omit he hs in
lemma speed (hy:x∈ S!): ‖Tilt.regal (crownP F M Z) (P! x) 1‖ ≤ Φ/t₁*z0+(P+B)/t:=by
    let hx:= hires Z M hq -- order
    rw [show P! x= stamp F G (A! x) from rfl,glossY F R v J X Y U' t Z ρ M hp hz]
    exact (norm_add_le ..).trans (add_le_add (hx.trans (mul_le_mul_of_nonneg_left ho (div_nonneg (Cane.specs M hq) (by positivity)))) ((stun F _).trans (localB F R v J χ X Y U' t Z ρ h ht x hU hp hK hG hc hX hy)))
local notation "Ξ"=> Φ/t₁*z0+(P+B)/t
lemma carve (hv: z0 ≤ O.outer) (hy:B'*z0+(P+B)/t≤ O.outer) (hu:shade G*(B'*z0+(P+B)/t) ≤ O.r) (hι:shade G*(ι*z0)≤ O.r)
     (hz0:(Φ/t₁*z0+(P+B)/t)+ O.b*t*O.r^2 ≤ O.w) (hx': (Φ/t₁*z0+(P+B)/t)< O.w/2) : (∀ i:Body 1 f,‖ran (crownP F M Z) i‖≤ O.r) ∧ (∀ x :SpaceP F X G, x∈ S! → ‖meetVar Z (A! x)‖ ≤ O.outer ∧ ‖tint G _ (P! x)‖ ≤ O.r ∧ ‖Tilt.regal s! (P! x) 1‖ + O.b*t*O.r^2 ≤ O.w ∧ ‖Tilt.regal s! (P! x) 1‖ < O.w/2):=by
    refine ⟨fun i=>(tends F R v Z ρ M he hs ho i).trans hι,fun i h_v=>?_⟩; have hp':= whirl F R v J χ X Y U' t Z ρ h ht i hU M hp hK hG hc hX he hs ho h_v; have hx:= Ruby.speed F R v J χ X Y U' t Z ρ h ht i hU M hp hz hK hG hc hX hq ho h_v
    rw [norm_meet]; exact ⟨max_le (ho.trans hv) (hp'.trans hy), (tint_le _).trans ((mul_le_mul_of_nonneg_left ((stun F _).trans hp') (shade_pos _).le).trans hu), (add_le_add_left hx _).trans hz0,hx.trans_lt hx'⟩
end YM.MSbar.Ruby
