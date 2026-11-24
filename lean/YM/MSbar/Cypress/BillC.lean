import YM.MSbar.Cypress.Vibe
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
noncomputable def rollW (s:Site f→ G.Color) (x:Positions (Key F G)):= grad s + Rolling.stamp F G x
local notation "Φ₁"=> rollW F g!
local notation "Q"=> rollW F s
local notation "V'"=> Primary f G
variable (hS:Parma.Station F v ρ R.path R.clip (installed S.ratio M) n B' c₁ c₂ c₃ c₄) (hb:0 ≤ B') (hx:Cane M A0 A' a E σ κ) -- check
lemma pasture : lightP F R v t ρ T' g s p = Lodge.shore (fieldLaw Γ) ((Rolling.stamp F G).comp (center F ρ)) (rollW F s) (film R T' t p ∘ Lodge.Clamp g):=by
     unfold lightP Lodge.shore Spruce.pegged Tilt.regal; simp_rw [map_add, one_smul]; apply _root_.funext; intro x; refine integral_congr_ae (Eventually.of_forall (fun u=>?_)); apply congr_arg; unfold rollW; change Rolling.stamp F G u + Rolling.stamp F G _+_= grad s+_+ Rolling.stamp F G _; exact add_right_comm .. |>.trans (by abel) -- function variable
lemma mellow(x:x!) : roll S.ratio M G x=maple M' G*ᵥ x:=by
    funext i; change (∑ j:V, pension S.ratio M G [] i j*x j)=∑ j:V,maple M' G i j*x j; apply Finset.sum_congr rfl; intro j h; simp only [pension,Tramp.maple,Matrix.of_apply]; by_cases hx:j.2=i.2; rw [if_pos hx,if_pos hx.symm];rfl; rw [if_neg hx,if_neg (Ne.symm hx)]
include hz h0
lemma pose (u:Positions (Key F G)) : rollW F (crownP F M Z) u+((Rolling.stamp F G).comp (center F ρ)) Z= roll S.ratio M G Z+Rolling.stamp F G u:=by
    rw [rollW,mellow M,ContinuousLinearMap.comp_apply, vaultT F M' Z ρ R.clip R.path hz h0]; unfold crownP; rw [basePoint,show grad _= -grad (tint G _ (runner (straighten S F M') G*ᵥ Z)) from ?_,← euclid]; · abel
    let U:= tint G _ (runner (straighten S F M') G*ᵥ Z); unfold grad; rw [← map_neg ((Wave.panel G f).symm)]; congr 1; funext i; change - (U _) - - (U _) = -(_-_); abel
variable (i:Primary c G)
noncomputable def aKey (x:Primary c G):=cardsH G f (mouth F (installed S.ratio M) 0 G *ᵥ bolt x)
lemma poles : P₁ (bolt i)-P₀ (bolt i)=grad (aKey F M i):=by rw [mellow M, ContinuousLinearMap.comp_apply, vaultT F M' (bolt i) ρ R.clip R.path hz h0]; unfold aKey; rw [basePoint, ← euclid]
omit hz h0
local notation "C0"=> Cards G f
lemma pump {σ ι:Type}[Fintype σ][Fintype ι][DecidableEq ι]{l:σ→Site f}{L:ι→ Site f}{G:Matrix σ ι ℝ}(h:Syrup l L a n G r)(ha:0≤a) (i:ι) : ∑ j:σ, |(G *ᵥ Uniform.bolt i) j| ≤ r:=by
    have hp:=h.rightP i; refine le_trans ?_ hp; apply sum_le_sum; intro j _; unfold skim; apply le_trans (le_of_eq _) (le_mul_of_one_le_left (abs_nonneg _) _); · simp [bolt,Pi.single_apply,mulVec,dotProduct,mul_ite]
    exact (show 1≤ Measuring.factor a n 0 from (by simp [Measuring.factor])).trans (inc n ha le_rfl (by positivity))
lemma psum (v:G.Color):‖v‖ ≤ ∑ i:G.ColorIndex,|v i|:= by
     rw [← (EuclideanSpace.basisFun G.ColorIndex ℝ).sum_repr' v]; refine (norm_sum_le ..).trans ?_; rw [(EuclideanSpace.basisFun G.ColorIndex ℝ).sum_repr' v]; simp only [norm_smul, EuclideanSpace.basisFun_repr,OrthonormalBasis.norm_eq_one,mul_one]; simp_rw [← OrthonormalBasis.repr_apply_apply]; simp
include hS hb
lemma presses : ∑ j:Site f, ‖aKey F M i j‖ ≤ c₁:=by
     let w:= mouth F M' (0:ℝ) G *ᵥ Uniform.bolt i; let H':Site f ×G.ColorIndex→C0:= Sum.inr ∘ Sum.inl; have ht:= pump (hS.mouth 0 (by simp)) hb i
     have he:∑ j:Site f, (∑ k:G.ColorIndex,|aKey F M i j k|) ≤ c₁:=by
         rw [←Fintype.sum_prod_type']; exact (Spruce.subtot H' (Sum.inr_injective.comp Sum.inl_injective) (fun i:C0=> |w i|) (fun _=>abs_nonneg _)).trans ht
     exact (sum_le_sum (fun j _=> psum ..)).trans he
noncomputable def powerW (G:Gauge)(c:ℝ):= (Fintype.card G.ColorIndex:ℝ)*(Fintype.card (Fin 4):ℝ)*(c+c)
lemma bondsK : atoms (aKey F M i) ≤ Fintype.card G.ColorIndex * ((Fintype.card (TypeFace 1):ℝ)*(c₁+c₁)):=by -- TypeFace ∼axes
     let φ:=aKey F M i; have hm:=presses F R v ρ M hS hb i; have hf(r): ‖ran φ r‖≤ ‖φ r.1‖+‖φ (r.1+step (axisEquiv.symm r.2))‖:= max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _)); unfold Aqua.atoms; rw [Fintype.sum_prod_type]; simp_rw [Finset.sum_const,nsmul_eq_mul, Finset.card_univ,← Finset.mul_sum]; apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _); rw [Fintype.sum_prod_type,sum_comm]; rw [← nsmul_eq_mul,← Finset.card_univ,← sum_const]; apply sum_le_sum; intro j _; refine (sum_le_sum (fun i _=>hf (i,j))).trans ?_; rw [sum_add_distrib ]; exact add_le_add hm ((Equiv.sum_comp (Equiv.addRight (step (axisEquiv.symm j))) (fun (p:Site f)=> ‖φ p‖)).trans_le hm)
lemma bud : (∑ i':Primary f G, |P₁ (bolt i) i'|) ≤ c₂ ∧ ∑ i':Primary f G, |P₀ (bolt i) i'|≤ c₁:=by
     have hz : ∑ j:P0, |center F ρ (bolt i) j| ≤ c₂:=by
            let h:= poring F ρ*ᵥ bolt i; let f(j):=|h j|; have he(j:Key F G):f (.inr j)= |center F ρ (bolt i) j|:=by unfold f h poring; rw [LinearMap.toMatrix'_mulVec]; rfl
            simp_rw [←he]; exact (Spruce.subtot (Sum.inr:Key F G→Joint F G) Sum.inr_injective f (fun _=>abs_nonneg _)).trans (pump hS.land hb i)
     constructor
     · let v:=P₁ (bolt i); let I:=univ.image (pegKey (G:=G) F); change ∑ i,|v i|≤ _; rw [← Finset.sum_subset (s₁:=I) (subset_univ _) ?_, Finset.sum_image (fun _ _ _ _ h=> pin_key F h)]; rotate_left
       · rintro ⟨⟨j,k⟩,v1⟩ _ hh; obtain ⟨k,rfl⟩:= axisEquiv.surjective k; by_cases he:(j,k)∈F.trunks; · change |Rolling.stamp F G _ ((j,coord k),v1)|= _; rw [ruler,dif_pos he,abs_zero]; -- coord unqual
         exact False.elim (hh (Finset.mem_image.mpr ⟨(⟨(j,k),he⟩,v1),mem_univ _,rfl⟩))
       apply le_trans (le_of_eq ?_) hz; apply sum_congr rfl; intro j _; change |Rolling.stamp F G (center F ρ (bolt i)) (pegKey F j)|=_; unfold pegKey; rw [ruler,dif_neg j.fst.prop] -- era
     let i':Primary f G→Cards G f:= Sum.inl; let uj:= mouth F M' 0 G *ᵥ bolt i; have hp(j:Primary f G):uj (i' j)= roll _ M G (bolt i) j:=by
         change cards0 G _ uj j=_; rw [show cards0 _ _ _=_ from turnPoint F M' _ _,mellow M]; unfold plot; simp only [sub_zero,one_smul,zero_smul, add_zero]
     simp_rw [← hp]; exact (Spruce.subtot i' Sum.inl_injective (fun i:Cards G _ =>|uj i|) (fun _=>abs_nonneg _)).trans (pump (hS.mouth 0 (by simp)) hb _)
end YM.MSbar.Cypress
