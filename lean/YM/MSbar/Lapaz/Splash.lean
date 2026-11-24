import YM.MSbar.Lapaz.Pockets
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Lapaz
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal
open Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Bakery.Film
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
omit h ht hU
noncomputable def vene (X:Support f) (F:Forest S.ratio)(G:Gauge):Matrix (Joint F G) (Lake F X G) ℝ := Rolling.straight F G* imbed (includeX F X)
lemma venue :meetVar Z (berth F R v J X Y U' Z t u)= meetVar Z (berth F R v J X Y U' Z t 0)+ vene X F G *ᵥ u:=by
    rw [show vene X F G *ᵥ u=_ from (show vene X F G *ᵥ u=Rolling.straight _ _ *ᵥ((imbed Λ)*ᵥ u) from (Matrix.mulVec_mulVec u (Rolling.straight F G) (imbed Λ)).symm)]; unfold berth; rw [Rolling.straight, LinearMap.toMatrix'_mulVec, Matrix.mulVec_zero,add_zero]; change _=meetVar _ _+ meetVar (0:Positions V) _; unfold meetVar; rw [← map_add, Prod.mk_add_mk,add_zero];rfl
lemma vision (U:X₀): ‖vene X F G *ᵥ U‖ ≤ ‖U‖:=by
    let Z:=imbed Λ; have hv:‖Z *ᵥ U‖ ≤ ‖U‖:=by
        refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=>?_ ; by_cases hh:i∈ Set.range (Λ); obtain ⟨a,rfl⟩:=hh; rw [show (Z*ᵥU) _=U a from congr_fun (shares Λ (secureY F X G) U) a]; exact norm_le_pi_norm U a; rw [show (Z*ᵥU) i=0 from inactive _ _ hh U]; simp
    rw [show vene X F G *ᵥ U = Rolling.straight F G *ᵥ ((imbed Λ)*ᵥU) from (Matrix.mulVec_mulVec U (Rolling.straight F G) (imbed Λ)).symm, Rolling.straight,LinearMap.toMatrix'_mulVec]; change ‖meetVar (0:x!) (Z *ᵥ U)‖≤_; rw [norm_meet,norm_zero]; exact max_le (norm_nonneg _) hv
lemma vertical :Continuous (berth F R v J X Y U' Z t):= Continuous.add continuous_const ((toLin' (imbed Λ)).continuous_of_finiteDimensional)
local notation "L₀"=> meetVar Z (berth F R v J X Y U' Z t 0)
local notation "Φ"=> venue
section
variable (Q':PowerSeries (Pot (Joint F G)))
lemma rebate : taste p (picture (meetVar Z (berth F R v J X Y U' Z t u)) Q') t- taste p (picture (L₀) Q') t = taste p (micro (L₀) (vene X F G) (Rewind Q' L₀) u) t:=by
    unfold micro; rw [←venue F R v J X Y U' t Z u]; unfold taste picture; simp_rw [PowerSeries.coeff_map,Rewind,PowerSeries.coeff_mk, Bakery.rewind,_root_.map_sub, MvPolynomial.eval_C,mul_sub, Finset.sum_sub_distrib]
local notation "σ"=>PowerSeries.coeff
local notation "Y'"=> keepB F X G
variable {b s r k:ℕ}{α r0 r1:ℝ}
variable (hq:∀ i≤p,Tokew (address F G) α b k 0 (PowerSeries.coeff i Q') A∧ (PowerSeries.coeff i Q').totalDegree ≤ k)
variable (hp:0 ≤ α)(hr:‖meetVar Z (berth F R v J X Y U' Z t 0)‖ ≤ r1)
include hq hp hr
noncomputable def loftM (p m N:ℕ)(A r:ℝ):= (((p+1:ℕ):ℝ))*(A*(1+r)^(m+1)*N)
lemma portion : Belt p (micro (meetVar Z (berth F R v J X Y U' Z t 0)) (vene X F G) (Rewind Q' L₀) u) ≤ loftM p k (keepB F X G).card A r1*(1+‖u‖)^(k+2):=by
     let v':=vene X F G; let T':= t; let a:= L₀; let Y₁:= L! u; have hx:Y₁=a+ v' *ᵥu:= venue F R v J X Y U' t Z u; have hz := Jade.ahead F R v J X Y U' t Z 0 u; let V':=r1+‖u‖; let y!:=1+r1; let g(j):= σ j Q'; have hk : ‖Y₁‖≤V':=by unfold V'; rw [hx]; exact (norm_add_le ..).trans (add_le_add hr (vision F X u)); -- order
     have ht : 0 ≤ A:=(hq _ le_rfl).1.1; have hR:0≤ r1:= (norm_nonneg _).trans hr
     have hh(i:ℕ)(hi:i≤p)(X:T)(hX:‖X‖≤ V')(j:Joint F G): |fderiv ℝ (fun z=>eval z (g i)) X (bolt j)|≤ A*(1+r1)^(k+1)*(1+‖u‖)^(k+1):=by
          obtain ⟨he,hg⟩:=hq i hi; have hz : |eval X (pderiv j (σ i Q'))|≤ A*(1+V')^(k+1):= Bout.looks hp (Bout.across X (he.2 j) hp (by rwa [sub_zero]) (pdeg _ (hg.trans (Nat.le_succ _))) 0); rw [dimY,dintX]; refine hz.trans ?_; rw [mul_assoc A, ← mul_pow]; apply mul_le_mul_of_nonneg_left _ ht; unfold V'; gcongr; nlinarith only [mul_nonneg hR (norm_nonneg u)]
     have hD : Tilt.moves a Y₁ ≤ (Y').card* ‖u‖:=by
          have hV : ‖Y₁-a‖ ≤ ‖u‖:=by rw [hx, add_sub_cancel_left]; exact vision F X u
          unfold Tilt.moves; rw [← Finset.sum_subset (Finset.subset_univ Y') (fun i hi hx=>?_ )]; · exact (sum_le_sum fun i _=> show |Y₁ i-a i| ≤‖u‖ from (norm_le_pi_norm (Y₁-a) i).trans hV).trans_eq (by rw [sum_const,nsmul_eq_mul])
          change |Y₁ i-a i|=0; rw [show Y₁ i=a i from hz i (Finset.mem_sdiff.mpr ⟨hi,hx⟩), sub_self,abs_zero]
     let q(u):=tint G _ (A! u); let Z':=Metric.closedBall (0:T) V'; let G₁:= A*y!^(k+1)*(1+‖u‖)^(k+1);
     unfold Belt; have ht(j:ℕ)(hi:j∈range (p+1)) : |σ j (micro a v' (Rewind Q' a) u)| ≤ G₁*((Y').card *‖u‖) :=by
          unfold micro picture Rewind; rw [PowerSeries.coeff_map,PowerSeries.coeff_mk, rewind,← hx,map_sub,MvPolynomial.eval_C]; refine (Tilt.allV (fun x=> eval x (σ j Q')) Z' (convex_closedBall ..) (fun x _=>(vent ..).differentiable (by simp) x) (fun x he=>hh _ (Nat.lt_succ_iff.mp (mem_range.mp hi)) x (mem_closedBall_zero_iff.mp he)) (mem_closedBall_zero_iff.mpr (hr.trans (le_add_of_nonneg_right (norm_nonneg _)))) (mem_closedBall_zero_iff.mpr hk)).trans (mul_le_mul_of_nonneg_left hD (by positivity))
     apply (sum_le_sum ht).trans; rw [sum_const,card_range,nsmul_eq_mul]; unfold loftM; change (_:ℝ)* _≤ _; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (Nat.cast_nonneg _)) (by unfold G₁ y!;positivity)) (by positivity)).trans_eq ?_; unfold G₁ y!;ring
end
end YM.MSbar.Lapaz
