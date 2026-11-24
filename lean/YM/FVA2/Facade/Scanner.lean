import YM.FVA2.Facade.Holding
/-!
 # Splice a joint, including the full conditional denominator

 * No look-ahead beyond this step required.  `U.W`, `Q` and transported fields are
   at full **open-field** values, using native log coordinates on each mesh (all in the
   common `g` convention, for quoting/comparing with the controlled leading parameters).
 * Gauge if so chosen at terminal; not used here. Exact identity irrespective of number
   of layers. In particular `pending` excludes both open-bottom and Haar therein.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Facade
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter MeasureTheory PertExtension Precision Lattice GaussianScore PowerSeries Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open scoped Classical Topology BigOperators ContDiff ENNReal
variable {G: Gauge} {c f n:Side}
variable {S: StepData c f}{U:Fabric G c} {H:S.patch.Branches S.kernel G}{hf: Even f.val}{t:S.Choices}{P:Inside S.ratio}{C:Cloth U}
local notation "T0"=> Cloth.inLayer (t:=t) (b:=H) (h:=hf) P C
local notation "T'"=> tollFirst (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
local notation "Ξ" => credit (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
local notation "π₃"=> descend (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)
local notation "F"=> Cross (G:=G) S P
local notation "Ω"=> Entry T0

variable (z:(layer S H t hf U).Cost→PowerSeries ℝ) (K:Unmasked G f)
variable (h:(core (gated P K t (z none))).RespectsPrice) (J:ChartRatio G)
local notation "y"=> gated P K t (z none)
local notation "V"=> policy T0 z K
local notation "X₀"=> LinearMap.fst ℝ (Panel T0) (Flats G (Bottom (layer S H t hf U)))
local notation "X₁"=> LinearMap.fst ℝ (Panel C) (Flats G (Bottom U))
local notation "κ"=> Update P t J (z none) K h
local notation "Ω₂"=> policy C (z∘some) κ

lemma valued (x w u) : (V).flourish (Ξ (x,w),u)= (y).flourish (x,line C (w,u))+(unpaid C (z ∘ some)).flourish (w,u):= by
 unfold policy; change K.Q.flourish (line (T0) (Ξ (x,w),u))+(unpaid _ _).flourish _= (K.Q.flourish (extend P x)+_)+_; rw [lined,add_assoc]; congr 1
 unfold unpaid; rw [bought,bought]; change ((∑ i:Option U.Cost,(Quadratic.genesis (z i) (valve T0 i)).flourish (Ξ (x,w),u))=_); rw [Fintype.sum_option]
 rw [show valve T0 none= (substep P t ∘ arrows) from rfl, ←payments arrows _ _ (subReady P t H), arrived]; congr 1; apply Finset.sum_congr rfl; intro i hi; rw [show valve T0 (some i)=valve C i ∘ π₃ from rfl, ← payments π₃ _ _ (valved C i), descending]; rfl

lemma bidding : Charged Ξ (core y) V Ω₂ ((skew _ h) ∘ₗ line C):= by
 refine ⟨fun x w u=> ?_⟩;  rw [valued,LinearMap.comp_apply]; erw [ordinary_square _ h x (line C (w,u)),add_assoc]; rfl

-- hair of Warm terminal excludes T̄ floor. Exact assembly.
lemma jac (x w) : jacobian J (Ξ (x,w))= jacobian J x *jacobian J w:= by unfold Chart.jacobian; change (∏ i:Blocking.Index S P ⊕ Warm C,_)=_; rw [Fintype.prod_sum_type]; rfl

lemma tissued (hj:LocalRatio J) : boost X₀ (tissue J (Warm T0))= boost (T') (tissue J (Blocking.Index S P)) * boost (X₁ ∘ₗ π₃) (tissue J (Warm C)):= by
 let a:= jacobian J (U:=Blocking.Index S P)
 let b:= jacobian J (U:=Warm C)
 let f:= jacobian J (U:=Warm T0); let u:= T'; let q:= X₁ ∘ₗ π₃
 have he:f ∘ X₀=(a ∘ u)*(b ∘ q):= by
      ext1 ⟨x,k⟩; obtain ⟨⟨x,w⟩,rfl⟩:= (Ξ).surjective x
      change jacobian J (Ξ (x,w))=a (_)*b (q (Ξ (x,w),k)); unfold q u; simp only [chargedFirst,LinearMap.comp_apply,descending]; exact jac J x w
 have h₀ : f 0=a 0*b 0:= by
     have hw := jac (P:=P) (C:=C) (t:=t) (H:=H) (hf:=hf) J 0 0; rw [Prod.mk_zero_zero,map_zero] at hw; exact hw
 unfold tissue; simp_rw [map_mul,boost_c, Vault.climbing X₀ ((Ratio.jacobian_smooth hj).of_le le_top), Vault.climbing (T') ((Ratio.jacobian_smooth hj).of_le le_top),Vault.climbing (X₁ ∘ₗ π₃) ((Ratio.jacobian_smooth hj).of_le le_top)];
 rw [show jacobian J (U:=Warm T0)= f from rfl,h₀,he,rise_mul ((leaned u (Ratio.jacobian_smooth hj)).of_le le_top) ((leaned q (Ratio.jacobian_smooth hj)).of_le le_top), mul_inv]; unfold roll; simp_rw [map_mul]; unfold a b u q; ring
lemma packer : packed T0 z= boost (arrows (H:=H) (hf:=hf) (t:=t) (P:=P) (C:=C)) (chip (z none) (substep P t))* boost π₃ (packed C (z∘some)):= by unfold packed; change (∏ i:Option U.Cost,_)=_; rw [Fintype.prod_option,map_prod,show valve T0 none=substep P t ∘ arrows from rfl,←pullPay arrows _ _ (subReady P t H)]; congr 1; exact Finset.prod_congr rfl fun i _=>(pullPay π₃ (z (some i)) _ (valved C i)).symm

lemma prestate (hj:LocalRatio J)(x w u):
 Stack.read (Ξ (x,w),u) (ledge T0 z J K)= Stack.read (x,line C (w,u)) (receipt P t J (z none) K)* Stack.read (w,u) (pending C (z ∘ some) J):= by
 unfold ledge pending receipt; rw [packer z,tissued J hj]; simp_rw [_root_.map_mul,caught]; rw [arrived,descending,chargedFirst,LinearMap.comp_apply,descending,lined];
 erw [map_mul (Stack.read (w,(u:Flats G (Bottom U)))),caught X₁ (tissue J (Warm C))]
 let a:= Stack.read (extend (G:=G) P x) K.W; let b:= Stack.read (x,line C (w,u)) (chip (z none) (substep P t)); let g:= Stack.read ((w,u): Entry C) (packed C (z ∘ some)); let p:= Stack.read x (tissue J (Blocking.Index S P)); let q:=Stack.read w (tissue J (Warm C)); change a*(b*g*(p*q))=a*p*b*(g*q); ring

local notation "σ"=> tangent G (Blocking.Index S P)
local notation "μ"=> tangent G (Warm T0)
local notation "ρ"=> tangent G (Warm C)
local notation "ha(" p ")" => (Charged.ticket (bidding z K h J) h p)
lemma sails (A:Ticket (Flats G f)) (hh: (core (Ω₂)).RespectsPrice)(hj:LocalRatio J)(u:incline K.W) : uptake (V) μ ha(hh) (ledge T0 z J K * boost (line T0) A) = uptake (Ω₂) ρ hh (ledge C (z∘some) J (κ) * boost (line C) (Broadcast P t J (z none) K h (boost (blankRight P) A))) := by
 let d:= boost (blankRight (G:=G) P) A; let p:= receipt P t J (z none) K
 refine (Charged.process (π:=line C) h ha(hh) hh (bidding z K h J) σ μ ρ (p:=ledge T0 z J K * boost (line T0) A) (f:=p*d) (g:=pending C (z∘some) J) (fun x w u=> ?_)).trans ?_
 · erw [_root_.map_mul,prestate z K J hj, caught (line T0) A, lined, mul_right_comm];
   erw [map_mul (Stack.read (x,line C (w,u))) p d,caught (blankRight P) A]; rfl
 unfold ledge; rw [mul_right_comm, ←(boost (line C)).map_mul]; unfold Broadcast Update; rw [fit_eq (gated P K t (z none)) σ h d p (along hj (z none) u)]

lemma ticketed (hh:(core (Ω₂)).RespectsPrice)(hj:LocalRatio J) : uptake (V) μ ha(hh) (ledge T0 z J K) = uptake (Ω₂) ρ hh (ledge C (z ∘ some) J κ) := Charged.process (π:=line C) h ha(hh) hh (bidding z K h J) σ μ ρ (p:= _) (prestate z K J hj)
end YM.FVA2.Facade
