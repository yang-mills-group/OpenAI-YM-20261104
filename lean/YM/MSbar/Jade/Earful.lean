import YM.MSbar.Jade.Crook
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Jade
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal
open Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Bakery.Film
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
variable (hβ:R.beta=t⁻¹^2)(hx:x∈clipM F X Y (hotel F X Y J (postcard G c t Z) (vest (priced F v R.clip R.path) (t • Z)) A B) χ t (sampleY F R v J X Y U' (t • Z) ∘ includeX F X) U') (hx':u∈clipM F X Y (hotel F X Y J (postcard G c t Z) (vest (priced F v R.clip R.path) (t • Z)) A B) χ t (sampleY F R v J X Y U' (t • Z) ∘ includeX F X) U')
variable (hχ:LocalRatio χ)(hX:X ⊆ Y)(hg:Clear G J)
variable {z:ℝ→ Config G f→ℝ}(hh:Trend z H' R.path R.clip p) 
variable (ha:S.patch.Branches S.kernel G)(hG:Critical F R.clip R.path ρ)(hT:ClassicalMatch F R.clip l R.path e ρ)
include hx hx' hX hg hχ hh ha hG hT hβ
-- currencies detailed.V.Domain k block uniform.Needs Scope later. Use Energy price.R orientation F.Tech.Recoil
structure Vows (G:Gauge)(F:Rep G f)(H': Nesting G f)(χ:ChartRatio G)(B':Forest S.ratio)(v:S.Choices) (p m:ℕ) (t a b cξ d r r1 r2 r3 r4 bb C D A Z U w:ℝ):Prop where
    e : t ≤ 1
    posB :0≤ bb
    posC: 0≤ C
    posD: 0 ≤ D
    shape: p+3≤ m
    guide: Tilt.Guide G a b
    tune: ∀ i≤p,Aqua.Stone G i 2 cξ d
    hi:1 ≤ r2
    beam:3*r+b*t*r^2 ≤ r2
    hp0:t*r2<cξ
    hp1:t*r < a
    hp2:t*r < cξ
    hp3:t*r1<r4
    tors:∀ i≤p,∀ x:Positions (Primary f G), ‖tint G _ x‖≤ r2 → ∀ j: Primary f G, |fderiv ℝ (atlas H' p i F.path F.clip) x (bolt j)|≤ bb ∧ ∑ u:Primary f G,|buoy (atlas H' p i F.path F.clip) x [u,j]| ≤ bb
    sC:∀ x:Positions (Primary f G),x∈ Metric.closedBall 0 w → ContDiffAt ℝ (↑(2:ℕ)) (film F H' t p) x ∧ (∀ i:Primary f G,|fderiv ℝ (film F H' t p) x (bolt i)|≤ U) ∧ ∀ i:Primary f G, ∑ j:Primary f G,|buoy (film F H' t p) x [j,i]| ≤ U
    posU:0 ≤ U
    rank : ∀ i: Bond c, ∀ x:Positions (Joint B' G), ‖x‖ < r4→ Allows m (arch B' v i) x C -- c side collision
    actor :∀ i:B'.Free,∀ x:Positions (Joint B' G), ‖x‖<r4→ Allows m (signal B' i χ) x D
-- pay.W.Ex Ζ.Total card.
variable {a b c₀ d₀ r r1 r2 r3 r4 bb K1 K2 y₀ y₁ ω₁ w' U₀ :ℝ}{m n τ:ℕ}
noncomputable def rentM (v:Patch)(G:Gauge)(b d r bb K1 K2 t A w Y u:ℝ)(W₀ F' p:ℕ) := (u * ((F'*G.lieDim:ℕ)*(2*(b*t*r^2)))+u*(b*t*r^2)*((F'*G.lieDim:ℕ)*(2*w)) + Tilt.coal G p d r t Y bb *((F'*G.lieDim:ℕ)*(Y+Y))) + W₀*cities 4 (noiseCost v) * (2*K1*A^(2+p+1))*t^(p+1) + W₀*cities 4 0 * (2*K2*A^(p+1))* t^(p+1)
variable (T': Site f → G.Color) (T1:ℝ→ℝ)
local notation "τ'"=> Vows G R H' χ F v p m t a b c₀ d₀ r r1 r2 r3 r4 bb K1 K2 y₀ y₁ U₀ w'
local notation "Zρ"=>recoil F R v J X Y U' t Z H' p T' T1
set_option maxHeartbeats 400000 in
lemma logVic (hp: Vows G R H' χ F v p m t a b c₀ d₀ r r1 r2 r3 r4 bb K1 K2 y₀ y₁ U₀ w') (hk:Posture Q J F A B K w n τ X Y (t •Z) ν R.p)(hD:Touch R.eval)
     {o:ℕ} (hM:Lodge.Hat o w' E T1) (hs:∀ i: Body 1 f,‖ran T' i‖≤ r)
     (hQ:∀ i:SpaceP F X G,i ∈ S! → ‖meetVar Z (A! i)‖≤r1 ∧ ‖tint G _ (P! i)‖ ≤ r ∧ ‖Tilt.regal T' (P! i) 1‖ + b*t*r^2 ≤ w' ∧ ‖Tilt.regal T' (P! i) 1‖ < w'/2):
       let y:= barbed F v χ H'; let g(i:X₀):= taste p (picture (L! i) y) t
       |(F! x-F! u) -(g x-g u) -(recoil F R v J X Y U' t Z H' p T' T1 x- Zρ u)| ≤ rentM S.patch G b d₀ r bb K1 K2 t r1 w' r2 U₀ (keepB F X G).card (keepF F X).card p:=by
     intro y f'; obtain ⟨hz,hs0,h₀,hP⟩:=hQ x hx; obtain ⟨ht',hs1,h₁,hV⟩:=hQ u hx'
     have hg0 := Jade.eaves F v (L! x) (L! u) (keepB F X G) ha hp.hp3 ht hz ht' (ahead F R v J X Y U' t Z u x) p (by have h:=hp.shape;omega) hβ hp.rank; have hg1:= Jade.curled F χ (L! x) (L! u) _ hp.hp3 ht hz ht' (ahead F R v J X Y U' t Z u x) hχ p (by have h:=hp.shape;omega) (Jade.ballot F R v J χ X Y U' t Z h ht x hU hX hχ hg hx) (Jade.ballot F R v J χ X Y U' t Z h ht u hU hX hχ hg hx') hp.actor hp.posD
     unfold f' y; rw [show _-_= _ from Jade.fares F R v J χ X Y U' t Z e l ρ h ht u x hU H' p hβ hx hx' hχ hX hg hh ha hG hT (by exact (Posture.pose hg hk hx.1).2.2.2.1) (by exact (Posture.pose hg hk hx'.1).2.2.2.1), Jade.refurbish F R v J X Y U' t Z x H' p _ _ hM hP, Jade.refurbish F R v J X Y U' t Z u H' p _ _ hM hV]
     -- use abel to group
     have hE:= Tilt.Xact T' (P! u) R H' (P! x) p (keepF F X) hh hp.tune ht hp.e hp.tors hp.hp0 hp.hi hp.guide hp.hp1 hp.hp2 hs1 hs0 hs (pupil F R v J X Y U' t Z x u) hp.posB hp.beam h₁ h₀ hp.sC hp.posU hD
     rw [show _ + _ + _ - _ = _ from (show ∀ a b c d:ℝ,a+b+c-d=a-d+b+c from (fun a b c d=> by ring)) _ _ _ _];
     apply (abs_add_le ..).trans; apply add_le_add ((abs_add_le ..).trans (add_le_add hE hg0)) hg1
end YM.MSbar.Jade
