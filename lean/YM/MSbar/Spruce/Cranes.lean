import YM.MSbar.Spruce.Tide
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
noncomputable def pegged (z:Site f→G.Color)(F_:Positions (Primary f G)→ℝ)(x: Positions (Key F G)) := F_ (Tilt.regal z (Rolling.stamp F G x) 1)
noncomputable def pegKey (x:Key F G):Primary f G:= ((x.1.val.1,Exterior.coord x.1.val.2),x.2)
open Measuring
lemma pin_key : Injective (pegKey (G:=G) F) :=by
     intro x y he; have hp : x.fst.val.1=y.fst.val.1:= congr_arg (fun i:Primary f G=> i.1.1) he; have hY : x.fst.val.2=y.fst.val.2:= axisEquiv.injective (congr_arg (fun i:Primary f G=> i.1.2) he); exact Prod.ext (Subtype.ext (Prod.ext hp hY)) (congr_arg (fun i:Primary f G=>i.2) he)
lemma passes (x:Key F G): Rolling.stamp F G (bolt x)=bolt (pegKey F x):=by
     have hv(y:P0): Rolling.stamp F G (bolt x) (pegKey F y)= Uniform.bolt (pegKey F x) (pegKey F y):=by
          unfold pegKey; rw [ruler,dif_neg y.fst.prop]; change Uniform.bolt x y =Uniform.bolt (pegKey F x) (pegKey F y); simp only [bolt,Pi.single_apply,pin_key F|>.eq_iff]; by_cases h:x=y <;> simp [h,Ne.symm]
     funext i; obtain ⟨⟨j,k⟩,d⟩:=i; obtain ⟨k,rfl⟩:= Exterior.axisEquiv.surjective k; by_cases he:(j,k)∈ F.trunks
     · rw [show axisEquiv k=coord k from rfl,ruler,dif_pos he]; have ht : ((j,coord k),d)≠ pegKey F x:=by
           intro hu; apply x.fst.prop; have hp:j=x.fst.val.1:= congr_arg (fun i:Primary f G=> i.1.1) hu; have hv:k=x.fst.val.2:=axisEquiv.injective (congr_arg (fun i:Primary f G=> i.1.2) hu); rwa [hp,hv,Prod.mk.eta] at he -- mism
       simp [bolt,ht]
     exact hv (⟨(j,k), he⟩,d)
lemma peaced (F':Positions (Primary f G) →ℝ)(h0:FetchD (Measuring.chart f G) b a F') : FetchD (address F G ∘ Sum.inr) b a (pegged F s F'):=by -- parameter order
     let Hh:=fun y:Positions (Key F G)=> F' ( grad s+Rolling.stamp F G y)
     have hf : pegged F s F'=Hh:=by funext i; unfold Hh pegged Tilt.regal; rw [one_smul,add_comm]; -- grad K? def
     rw [hf]; exact fetch (grad s) (pegKey F) (Rolling.stamp F G) b (pin_key F) (passes F) F' h0
local notation "Φ"=>film R T' t p
local notation "P!"=>pegged F s (film R T' t p ∘ Lodge.Clamp g)
-- reef from fetch
lemma leeway {ι:Type}[Fintype ι][DecidableEq ι]{F:View ι→ℝ}(hF:Canopy F): Duel.Reef F 1:=by
    constructor; · exact hF.light
    constructor; intro l hl; cases l with
    | nil=> exact hF.whole
    | cons a v=> obtain rfl:v=[]:=List.eq_nil_of_length_eq_zero (by rw [List.length_cons] at hl; omega); obtain ⟨c,hV⟩:=hF.chart a; exact ⟨c,fun i=>by rw [budP _ [a] 1 i (show ContDiffAt ℝ (↑(1:ℕ)) F i from hF.light.contDiffAt) le_rfl]; exact hV i⟩
local notation "Z!"=> meetVar Z (0:Positions P0)
noncomputable def cup (S':Pot (Joint F G)):= Spruce.clasp (meetVar Z (0:Positions P0)) (imbed (Sum.inr:Key F G→Joint F G)) S'
lemma valet(k_:Pot (Joint F G)) (a:Positions (Key F G)): eval a (cup F Z k_)=eval (meetVar Z a) k_:=by
    unfold cup; rw [value]; congr 2; change meetVar Z 0+imbed (Sum.inr: Key F G→Joint F G) *ᵥ a= _; rw [← shrunk,Rolling.straight, LinearMap.toMatrix'_mulVec]; change meetVar Z 0+meetVar (0:x!) _=_; rw [meetVar,meetVar,← map_add,Prod.mk_add_mk,add_zero,zero_add];rfl
local notation "A'"=> berth F R v J X Y U' Z t
local notation "A0"=> berth F R v J X Y U' Z t 0
local notation "Λ'"=>imbed (includeX (G:=G) F X)
lemma keys (x:SpaceP F X G) : pen (berth F R v J X Y U' Z t 0) (imbed (includeX F X)) x= berth F R v J X Y U' Z t x:=by unfold berth pen; rw [Matrix.mulVec_zero,add_zero]
variable (L':List (Primary c G))
local notation "π"=>PowerSeries.coeff
local notation "η!"=>cycleP F v L'
variable (hp:Kind T')(hD1:(mold R F v).PosDef)
local notation "J'"=> barbed F v χ T'
local notation "η₀"=>cup F Z (PowerSeries.coeff 0 (cycleP F v L'))
local notation "K₁"=> hint (berth F R v J X Y U' Z t 0) (imbed Λ) (χ!) (pegged F s (film R T' t p ∘ Lodge.Clamp g))
local notation "j!"=>recoil F R v J X Y U' t Z T' p s g
include hD1 hp
variable (hc:Canopy (pegged F s (film R T' t p ∘ Lodge.Clamp g)))
include hc
lemma propR: Lapaz.cov (C:=χ!) (vene X F G) (barbed F v χ T') (cycleP F v L') (meetVar Z A0) (fun x=> recoil F R v J X Y U' t Z T' p s g x - recoil F R v J X Y U' t Z T' p s g 0) p=K₁ η₀ :=by
     let D:=χ!; let B:= cycleP F v L'; let g':=K₁; let P' :=η₀; let S':= P!; let Z':=meetVar Z A0; have hD : Matrix.PosDef (show Matrix _ _ ℝ from D) := (hD1.submatrix (secureY F X G)).inv; let W':=fieldLaw D -- syntax
     let f(x:X₀):=S' (pen A0 Λ' x); let V'(x:X₀):=eval (pen A0 Λ' x) P'; have he(x): j! x=f x:=(congr_arg S' (keys F R v J X Y U' t Z x)).symm
     have hv(x:SpaceP F X G):π 0 (micro Z' (vene X F G) B x)=V' x :=by unfold micro picture; rw [PowerSeries.coeff_map,← venue]; unfold V' P'; rw [keys,valet]
     have hg:π 0 (owes (vene X F G) D J' B Z' p)=∫ y,V' y∂ W':=by
          let Q:= J'; have hz:= well F v χ T' hp; have hy:=firm (vene X F G) hD Q B Z' (p:=p) hz 0 (Nat.zero_le p); let Uc:=Rewind Q Z'; have hT(x:X₀):Kind (micro Z' (vene X F G) Uc x):=by unfold micro Kind picture; rw [PowerSeries.coeff_map,hush hz,map_zero]; -- syntax
          have hV:π 0 (Lapaz.vow (vene X F G) D Q Z')=1:=by unfold Lapaz.vow picture; rw [PowerSeries.coeff_map,Cacao.covers (sugar _ (hush hz)),map_one]
          change (∫ y,π 0 (_ * Spring (micro Z' (vene X F G) Uc y)) ∂W')=π 0 (_ *Lapaz.vow (vene X F G) D Q Z') at hy; rw [elevator,sum_range_succ,sum_range_zero,zero_add,Nat.sub_zero,hV,mul_one] at hy; simp_rw [elevator,sum_range_succ,sum_range_zero,zero_add,Nat.sub_zero,fun x=>Cacao.covers (hT x),mul_one,hv] at hy; exact hy.symm
     have hW : Integrable (fun i=> f i*V' i) W':= paidHelp _ _ hD P' _ hc.light.continuous hc.whole; have hV:Integrable V' W':=(grille _ hD P' _ 1 (by norm_num)|>.integrable le_rfl); have hf:Integrable f W':=by
          have he:=paidHelp Λ' A0 hD (1:Pot P0) S' hc.light.continuous hc.whole; simp only [map_one,mul_one] at he; exact he
     unfold Lapaz.cov hint; change (∫ i,(j! i-j! 0)*π 0 (micro Z' (vene X F G) B i) ∂W')-(∫ i,j! i-j! 0 ∂W')*π 0 (owes _ D J' B Z' p)= (∫ i,f i*V' i∂W')-(∫ i,f i∂ W')*(∫ i,V' i∂ W'); simp_rw [show ∀ x:X₀, j! x=f x from he,hv,hg]; change (∫ i,(f i-f 0)*V' i∂W')-(∫ i,f i-f 0∂W')*(∫ i,V' i∂W') = _; simp_rw [show ∀ i : X₀,(f i-f 0)*V' i=f i * V' i-f 0*V' i from fun _=> sub_mul ..]; rw [integral_sub hW (hV.const_mul _),integral_sub hf (integrable_const (μ:=W') _),integral_const_mul,integral_const, probReal_univ, one_smul]; change _ = (∫ i,f i*V' i∂ W')-_; ring -- notation rhs
end YM.MSbar.Spruce
