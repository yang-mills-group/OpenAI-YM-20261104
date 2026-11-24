import YM.MSbar.Duel.PDrag
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Duel
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Further.GaussianScalar
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {σ ι τ:Type}[Fintype σ][Fintype τ][Fintype ι][DecidableEq ι][DecidableEq σ][DecidableEq τ]
variable {m p:ℕ}
local notation "µ"=> PowerSeries.coeff
local notation "P"=> Pot σ
local notation "Q"=> Pot ι
local notation "V"=> View σ
local notation "W"=>View ι
local notation "R"=> SpringK σ
-- concrete directional polynomial partial
local notation "H"=>SpringK σ
local notation "G"=>SpringK ι
local notation "B"=>View τ
variable (A:Matrix σ ι ℝ)(C': Matrix σ τ ℝ)(D:Matrix τ τ ℝ) (h:D.PosDef)
local notation "L"=> C'*D*C'.transpose
set_option quotPrecheck false
local notation "ν"=> PowerSeries.map (rail A).toRingHom
open MeasureTheory Set Metric
variable (F: View τ→ℝ)(T: View ι→L[ℝ] View τ)
variable (q:Pot σ)(x:View ι)(hf:Reef F 1)
local notation "ω'"=> fieldLaw D
local notation "Y"=>present A C'
local notation "j!"=> actor A C' F T
local notation "φ"=>faceA A C' F T
local notation "δ"=> fieldLaw D
include h hf
local notation "fA"=>fderiv ℝ
variable (M:ι→View τ)(b:ι→View σ)(K:Pot ι)(X₀:ι→Pot σ)(hM:Mold A C' D b M K X₀) (g:∀ i:ι,T (bolt i)=M i)(i:ι)
include hM g
lemma passion : fderiv ℝ (drag A C' D F T q) x (bolt i)= drag A C' D F T (dint (b i) q+X₀ i*q) x + (eval x (dint (bolt i) K))*drag A C' D F T q x:=by
    let m:=M i; let f(v:P):= actor A C' F T v x; have he(v:P) : Integrable (f v) δ:=fresh A C' D h F T v x hf; let V':= faceA A C' F T q x
    have hc:ContDiff ℝ 1 (f q):=(actorD A C' F T q hf).comp (f:=fun z:B=>(x,z)) (contDiff_const.prodMk contDiff_id)
    let q':= dint (b i) q; let E(y:B):= fderiv ℝ (f q) y m
    have hx(y:B): V' y (bolt i) = f q' y+ E y:=by
         change hPoke _ _ _ _ _ _ _ _= _+ tPoke A C' F T q m x y; rw [peaks A C' F T q x hf, twinge A C' F T q x hf,g,← hM.shift, dime]; unfold f q' m actor;rw [_root_.map_add, add_mul,add_assoc]
    obtain ⟨hu,h₀⟩:= paidRegion A C' D h F T q x hf; let v:=eval x (dint (bolt i) K); let w(y:B):= f (X₀ i*q) y+ v*f q y; let a:= (f q); have hv(y:B): dotProduct (D⁻¹ *ᵥ y) m*f q y=w y:=by unfold w f m v actor present; rw [_root_.map_mul,hM.score i x];ring
    have hV:= ((ContinuousLinearMap.apply ℝ ℝ (bolt i:W)).integrable_comp hu); have hh: Integrable E δ :=by rw [show E=(fun i'=> V' i' (bolt i)-f q' i') from funext fun i'=>by rw [hx]; ring]; exact hV.sub (he _)
    have ht:= Cacao.steamed h m hc.continuous (show Continuous E from (ContinuousLinearMap.apply ℝ ℝ _|>.continuous.comp (hc.continuous_fderiv (by simp)))) (he q) hh (by simp_rw [hv]; exact (he _).add ((he _).const_mul _)) (fun y=>?_)
    · have hV(y:B): actor A C' F T (q'+X₀ i*q) x y = f q' y+ f (X₀ i*q) y:=by unfold actor f; rw [_root_.map_add, add_mul];rfl
      rw [h₀.fderiv,ContinuousLinearMap.integral_apply hu]; change (∫ y,V' y (bolt i)∂δ)=_; unfold drag; change _ = (∫ y,actor A C' F T (q'+_) x y∂δ)+ v* (∫ y,f q y∂δ); simp_rw [hx,hV]; rw [MeasureTheory.integral_add (he _) (he _),MeasureTheory.integral_add (he _) hh,ht]; simp_rw [hv]; rw [show (∫ y,w y∂δ)=(∫ y,f (X₀ i*q) y∂δ)+v*(∫ y,f q y∂δ) from (by unfold w; rw [MeasureTheory.integral_add (he _) ((he _).const_mul _),integral_const_mul])];ring
    let V₀(t:ℝ):= y+t • m; have hs: HasDerivAt V₀ m 0:=by simpa only [zero_smul,one_smul,add_zero,zero_add] using! ((hasDerivAt_id' (0:ℝ)).smul_const m).const_add y
    have he: V₀ 0=y:=by unfold V₀; rw [zero_smul,add_zero]
    have ht:= ((hc.differentiable (by simp) (V₀ 0)).hasFDerivAt.comp_hasDerivAt (0:ℝ) hs); rw [he] at ht; exact ht
-- KL variation
variable (β:SpringK σ)(hp:Kind β)
local notation "O"=> ν (confect L β)
include hp
local notation "fs"=> readScore b X₀ β
lemma stall (l:List ι) : fA (drag A C' D F T (µ 0 (fs l))) x (bolt i)= drag A C' D F T (µ 0 (fs (i::l))) x + eval x (dint (bolt i) K) * drag A C' D F T (µ 0 (fs l)) x :=by
    rw [passion A C' D h F T _ x hf M b K X₀ hM g i]; congr 2 -- enlarge
    unfold readScore; rw [batt,_root_.map_add, flux,ride,elevator,sum_range_succ]; unfold flux; rw [_root_.map_add,ride,hp,_root_.map_zero]; simp -- conform
noncomputable def delta (b:ι→View σ)(X₀:ι→Pot σ)(β:SpringK σ)(l:List ι)(y:View ι):= drag A C' D F T (µ 0 (readScore b X₀ β l)) y
noncomputable def rake (l:List ι):= delta A C' D F T b X₀ β l
end YM.MSbar.Duel
