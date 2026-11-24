import YM.MSbar.Rolling.Revenue
import YM.MSbar.Rolling.Over
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Rolling
open Matrix MeasureTheory Filter Function Set Next.SectorChange Further.GaussianScalar
open Push Push.Uniform RG Wilson Gauge Lattice Tree Precision Metric Exterior Price
open scoped Topology Classical BigOperators ContDiff
variable {G:Gauge}{c f:Side}{S: StepData c f}(B: Forest S.ratio)(i:S.Choices)(R T:PathData G)(p q:Clip)(ρ:fieldDir G c 1→ AxisChart G B)
open Cacao Bakery Portal
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
local notation "µ"=> PowerSeries.coeff
local notation "ol"=>fieldDir G c 1
local notation "X"=> Positions (Primary c G)
local notation "N"=> Positions (Primary f G)
local notation "Y"=> Positions (Key B G)
local notation "Z"=> Positions (Joint B G)
local notation "V"=> Config G f
local notation "K"=> Push.Uniform.block (priced B i p R) 0
local notation "C"=> (Push.Uniform.block (priced B i p R) 0)⁻¹
local notation "ν"=> center B ρ
variable (J:ChartRatio G)(hJ:LocalRatio J)
variable (n m:ℕ)(A:PowerSeries (Pot (Primary f G))) (F:ℝ → Config G f→ℝ) (u:ℕ)
variable (hc:Serves S G) (hp:Critical B p R ρ) (hq:ClassicalMatch B p q R T ρ)
variable (ht:Trend F A R p u)
local notation "v!"=>flame B ρ n m
noncomputable def straight (G:Gauge) : Matrix (Joint B G) (Key B G) ℝ:= LinearMap.toMatrix' (lowerCol (ι:=Primary c G) (τ:=Key B G)).toLinearMap
noncomputable def throne (ρ:fieldDir G c 1→ AxisChart G B) : Positions (Primary c G)→L[ℝ]Positions (Joint B G):= (partSpace _ _).symm.toContinuousLinearMap.comp ((ContinuousLinearMap.id ℝ _).prod (center B ρ))
noncomputable def poring (ρ:fieldDir G c 1→ AxisChart G B) :=LinearMap.toMatrix' (throne B ρ).toLinearMap
noncomputable def song (ρ:fieldDir G c 1→ AxisChart G B) :Nesting G c :=PowerSeries.map (rail (poring B ρ)).toRingHom (confect (straight B G * (Push.Uniform.block (priced B i p R) 0)⁻¹ * (straight B G).transpose) (barbed B i J A))
local notation "M"=>song B i R p J A ρ
local notation "μ!"=>fieldLaw
local notation "i₀"=> Fintype.card (Key B G)
set_option quotPrecheck false
noncomputable def vital (v : ℝ)(x:Positions (Primary c G))(m:ℕ):=
   Real.exp (height c q T x)*(∫ z in urn (Rolling.fuel v ^ m) v, measureK B F v x z ∂B.order G)/(v ^Fintype.card (Key B G)*exitS (Push.Uniform.block (priced B i p R) 0) J)
variable (hK : Matrix.PosDef (Push.Uniform.block (priced B i p R) 0))
include hc hp hq ht hJ hK
lemma tavern (he:n < m)(hh:1 < m) : Price (yard n) (u+1) (fun t x=> vital B i R T p q J F t x m-taste u (picture x (Spring (song B i R p J A ρ))) t):=by
    let T':=v!; let W:=signing B ρ n m; let g x:= throne B ρ x; let L:= straight B G; have hL(w:Y): L *ᵥ w= meetVar (0:X) w:=by unfold L straight; rw [LinearMap.toMatrix'_mulVec]; rfl
    have hG(x y):peek B ρ (x,y) = g x+L *ᵥ y:=by
        rw [hL]; change (partSpace _ _).symm (_,ν x+y)= (partSpace _ _).symm (x,ν x)+ (partSpace _ _).symm (0,y); rw [←map_add,Prod.mk_add_mk,add_zero]
    let D:=barbed B i J A; let P:= M; let f₀(x:X)(t:ℝ):=taste u (picture x (Spring P)) t
    let z(x:X)(t:ℝ)(y:Y):=taste u (picture (g x+L*ᵥ y) (Spring D)) t; let C':=Push.Uniform.block (priced B i p R) 0; let Q:Matrix (Key B G) (Key B G) ℝ:=C'⁻¹; have hu:Kind D:= well B i J A ht.bond
    have hqE(x:X)(t:ℝ): f₀ x t= ∫ y,z x t y∂fieldLaw Q:=by
        unfold f₀ P song; rw [sunshine,ClearMain,poring,LinearMap.toMatrix'_mulVec]; have ht:= Portal.joint (g x) L D hK.inv hu D hu u t -- may `L` eval to
        have he(y:Y): Spring (micro (g x) L D y)=picture (g x+L*ᵥ y) (Spring D):= sunshine (MvPolynomial.aeval (R:=ℝ) (g x+L*ᵥ y))
        simp_rw [he] at ht; exact ht.symm
    -- above need rewrite integrand.Mix
    let X'(t:ℝ)(x:X):=den (ν x) (Rolling.fuel t ^m); have hr: Price (yard n (E:=X)) 0 (fun t x=>g x):= price_move (fun _ y=> y) ⟨n, Eventually.of_forall (fun x y hy=> (show ‖y‖ ≤ Rolling.fuel x ^ n from hy).trans_eq (by ring))⟩ (throne B ρ)
    have hP₀:∀ᶠ t:ℝ in Γ,∀ x:X,yard n t x→ {v:Y| ‖v‖ ≤ Rolling.fuel t}⊆X' t x ∧ MeasurableSet (X' t x):=by
        let k:= max n 1; filter_upwards [width, awake.eventually_ge_atTop (‖ν‖+2)] with t ⟨h₁,h₂,h₃⟩ h x ht; refine ⟨fun y hy=> ?_,(isClosed_le (continuous_const.add continuous_id|>.norm) continuous_const).measurableSet⟩; let b:= Rolling.fuel t; change ‖_+_‖≤ b^m
        apply (norm_add_le ..).trans; have hi:‖ν x‖ ≤ ‖ν‖*b^k:= (ContinuousLinearMap.le_opNorm ..).trans (mul_le_mul_of_nonneg_left ((show ‖x‖ ≤ _ from ht).trans (pow_le_pow_right₀ h₃ (le_max_left ..))) (norm_nonneg _)); have hu:‖y‖ ≤ b^k:= (show ‖y‖ ≤ b from hy).trans (by simpa using pow_le_pow_right₀ h₃ (show 1 ≤ k from le_max_right ..)); refine (add_le_add hi hu).trans (le_trans ?_ (pow_le_pow_right₀ h₃ (show k+1 ≤ m from (by unfold k;omega)))); rw [pow_succ]; linarith only [mul_le_mul_of_nonneg_right h (pow_nonneg (zero_le_one.trans h₃) k),pow_nonneg (zero_le_one.trans h₃) k]
    obtain ⟨τ,hτ⟩:= mort L hK.inv (Spring D) hr hP₀ u (u+1); obtain ⟨k,hk⟩:= early (fun t i=> peek B ρ i) W D u hu (torch B i R T p q ρ J hJ n m A F u hc hp hq ht) -- shadow hq
    let U:= exitS C' J; have hb:0<U:=perk J hJ K hK
    let φ:=fun t x=> purse (X' t x) (siteK B i R T p q J F ρ t x)
    refine Price.fixed (max τ k) 2 ?_; filter_upwards [width,hk,hτ, ht.base,hP₀, ((subs m).const_mul (shade G)).eventually (eventually_lt_nhds (show shade G*0< J.radius from (by rw [mul_zero]; exact hJ.patch)))] with t ⟨hx,hT,hd⟩ h' hV hs hM hr x hv
    let S'(z:B.Slice G):=measureK B F t x z; let T':= φ t x; let H:=height c q T x; obtain ⟨hA,hB⟩:= mint (ι:=B.Free) J (ν x) hJ C' hK H S' hx hr (show Envelope S' from ⟨(hutEnv (F t) hc hs.1 _).meas.comp (Tree.Forest.continuous_drape B).measurable, (hutEnv (F t) hc hs.1 _).cost.choose,fun i=>(hutEnv (F t) hc hs.1 _).cost.choose_spec (B.drape i)⟩) (fun i=>hutAlive (F t) hc hs.1 _ _)
    have hv': vital B i R T p q J F t x m = ∫ z,T' z∂fieldLaw Q:=by
        let W:= ∫ z,T' z∂fieldLaw Q; unfold vital; rw [show (∫ z in urn (Rolling.fuel t ^ m) t,measureK B F t x z∂ B.order G)=t^i₀*U *Real.exp (-H)*W from hB]; change Real.exp H * (t^_*U * _*W)/(t^_*U) = W; rw [Real.exp_neg]; field_simp
    change ‖vital B i R T p q J F t x m-f₀ x t‖ ≤ _; rw [hv',hqE]; let r:=t^(u+1); let g:= r* Rolling.fuel t^ k; have hg:0 ≤ g:=by unfold g r;positivity
    refine (Portal.ban _ _ hA (hM x hv|>.2) (z x t) (adapts L hK.inv ..) (fun _ h=> Set.indicator_of_notMem h _) (fun y hy=> ?_) hg (hV x hv)).trans ?_
    · unfold purse; rw [Set.indicator_of_mem (show y∈den _ _ from hy)]; unfold z; rw [← hG]; have he:= h' (x,y) ⟨hv,hy⟩; exact he
    rw [two_mul]; unfold g r; gcongr<;> first|exact le_max_left ..|exact le_max_right ..
end YM.MSbar.Rolling
