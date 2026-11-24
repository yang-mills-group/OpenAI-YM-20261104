import YM.MSbar.Jade.Money
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
-- support of tape.Size
omit h hU ht
noncomputable def keepB (G:Gauge): Finset (Joint F G):= Finset.univ.image (fun k:Lake F X G=> Sum.inr (includeX (G:=G) F X k))
noncomputable def keepF := (board F X).image (fun k => (k.val.1,Exterior.coord k.val.2))
local notation "B!"=>keepB F X G
local notation "Vμ"=>keepF F X
lemma ahead (j:Joint F G)(hi:j∈ Finset.univ\keepB F X G): meetVar Z (A! x) j= meetVar Z (A! u) j:=by
     cases j with|inl=>rfl|inr j=>
         change berth _ _ _ _ _ _ _ _ _ _ j= A! u j; have hz:j∉Set.range Λ:=by rintro ⟨a,hA⟩;apply (Finset.mem_sdiff.mp hi).2; exact Finset.mem_image.mpr ⟨a,mem_univ a, congr_arg _ hA⟩
         unfold berth; rw [Pi.add_apply,Pi.add_apply,inactive _ _ hz,inactive _ _ hz]
lemma currencyB : (keepB F X G).card ≤ X.card*4*G.lieDim:=by
     apply Finset.card_image_le.trans; simp only [card_univ,Lake,Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]; exact Nat.mul_le_mul_right _ (boardC F X)
lemma currencyF : (keepF F X).card ≤ X.card*4:=Finset.card_image_le.trans (boardC F X)
lemma pupil(k:Body 1 f)(he:k∉ keepF F X):tint G _ (P! x) k=tint G _ (P! u) k:=by
     rcases k with ⟨i,k⟩; obtain ⟨a,rfl⟩:= axisEquiv.surjective k; ext q; change stamp F G _ ((i,Exterior.coord a),q)= stamp F G _ ((i,Exterior.coord a),q); rw [ruler,ruler]; split; next h=> rfl
     next h'=> let k':F.Free:=⟨(i,a),h'⟩; have ht:k'∉board F X:=fun h=> he (mem_image.mpr ⟨k',h,rfl⟩); change meetVar Z (A! x) (Sum.inr (k',q))= meetVar Z (A! u) (Sum.inr (k',q)); -- (show meetVar Z (A! x) (Sum.inr (k',q))= meetVar Z (A! u) _ from ?_) -- check term
               apply Jade.ahead F R v J X Y U' t Z u x _; refine Finset.mem_sdiff.mpr ⟨mem_univ _,?_⟩; intro hp; obtain ⟨i,-,he⟩:=mem_image.mp hp; have hx : i.1.val= k':= Prod.ext_iff.mp (Sum.inr_injective he) |>.1; exact ht (hx ▸ i.1.prop)
noncomputable def recoil (z:Site f → G.Color)(g:ℝ→ℝ) :=fun x:SpaceP F X G=> film R H' t p (Lodge.Clamp g (Tilt.regal z (stamp F G (berth F R v J X Y U' Z t x)) 1))
lemma refurbish (z:Site f→ G.Color)(g:ℝ→ℝ) {m:ℕ} (hm:Lodge.Hat m E D g)(hx:‖Tilt.regal z (P! x) 1‖ < E/2) : recoil F R v J X Y U' t Z H' p z g x= film R H' t p (Tilt.regal z (P! x) 1):=by unfold recoil; refine congr_arg _ ?_; exact funext fun i=> hm.honest _ ((norm_le_pi_norm _ i).trans_lt hx)
end YM.MSbar.Jade
