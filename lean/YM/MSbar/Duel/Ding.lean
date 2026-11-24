import YM.MSbar.Duel.Dose
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
-- KL variation
variable (β:SpringK σ)(hp:Kind β)
local notation "O"=> ν (confect L β)
include hp
local notation "fs"=> readScore b X₀ β
local notation "gX"=> drag A C' D F T
local notation "Q!"=> delta A C' D F T b X₀ β
-- exponential output Jets θ.W.Vector polynomial ratio vs θ.A.Payment. Variation ∆ unselected
local notation "Θ"=> mystic K
local notation "V₀"=> port K O
variable (l:List ι)
lemma pull (t:ℕ) : ContDiff ℝ t (Q! l):=by
    have hv: Differentiable ℝ (Q! l):= fun x=> (paidRegion A C' D h F T (µ 0 (fs l)) x hf).2.differentiableAt
    induction t generalizing l with
    | zero => rw [Nat.cast_zero,contDiff_zero]; exact hv.continuous
    | succ a ih=>
        rw [Nat.cast_succ]
        refine contDiff_succ_iff_fderiv_apply.mpr ⟨hv,fun x=>?_ , fun x=>?_ ⟩
        · simp at x
        have he(i:ι)(y:W): fA (Q! l) y (bolt i)= Q! (i::l) y+eval y (dint (bolt i) K)*Q! l y:= stall A C' D h F T y hf M b K X₀ hM g i β hp l
        nth_rw 1 [Lis.spiral x]; simp_rw [_root_.map_sum,_root_.map_smul,he]; apply ContDiff.sum; intro i _; refine ((show ContDiff ℝ (↑a) (Q! (i::l)) from ?_).add ((vent (dint (bolt i) K)).of_le le_top |>.mul (ih l hv))).const_smul (x i)
        exact ih _ (fun x=> paidRegion A C' D h F T _ x hf|>.2.differentiableAt)
lemma wick : Q! [] x= Lodge.shore (fieldLaw D) T (fun y:View τ=> y) F x:=by unfold delta drag actor Lodge.shore readScore batt; simp
lemma year (l:List ι) : Q! l x= Yarn l.length (fun t:List Bool=> eval x (µ 0 (V₀ (takeout true t l))) * buoy (Lodge.shore ω' T (@id B) F) x (takeout false t l)):=by
    let f:= Q! []; let k:= port K O; have ht:f= Lodge.shore (fieldLaw D) T id F:= funext fun y=>wick A C' D h F T y hf M b K X₀ hM g β hp; have hz:= bob A C' D h F T x hf M b K X₀ hM g β hp l
    rw [mul_comm (Q! []), Lis.paisley l.length Θ _ _ _ ((vent K|>.of_le le_top|>.neg.exp).contDiffAt (x:=x)) (pull A C' D h F T hf M b K X₀ hM g β hp [] l.length|>.contDiffAt) le_rfl] at hz
    apply mul_right_cancel₀ (Real.exp_pos (-eval x K)|>.ne'); change Q! l x * Θ x= _ * Θ x; rw [hz, ← Measuring.poker]; refine stitch _ fun v hv=> ?_; rw [← atoms A C' D h F T x hf M b K X₀ hM g β hp]; rw [← ht]; change _ = _; unfold f; ring
-- variation Leib from Θ times; desired for log derivative recurrence. Cose_L := δL− A-zero_{L} δφ. Mixed `KL_n = polys + Cose`. Need identify relation:
-- for l++[i]: Q!l as above implies Cose_{i::L}= sum_S Cose°S * Θlog-stroke etc plus A_S*δF_{c+..}. use Leib derivative of compact formula
-- correction ∆ obeys cumulant recursion. LogΘ δ.P.
noncomputable def blast (l:List ι)(x:View ι) := delta A C' D F T b X₀ β l x-eval x (µ 0 (port K (ν (confect L β)) l))*delta A C' D F T b X₀ β [] x
-- local notation δ0.Tr.V
noncomputable def stallA (F: View ι→ℝ)(i:ι)(x:View ι):= fderiv ℝ F x (bolt i)
lemma dream (j:ι) : Q! (l++[j]) x=Yarn l.length (fun t:List Bool=> Q! (takeout true t l) x * buoy (fun y: W=> -(eval y K)) x ((takeout false t l)++[j])) + Yarn l.length (fun t:List Bool=> eval x (µ 0 (V₀ (takeout true t l))) * buoy (Q! []) x ((takeout false t l)++[j])) :=by
    let F'(v:View ι):= Q! [] v; let V':= mystic K; let Z:= F'*V'; let u(v:View ι):= -(eval v K); let q:=l.length; have hp': ContDiff ℝ (↑(q+1:ℕ)) F':= (Duel.pull A C' D h F T hf M b K X₀ hM g β hp [] (q+1)); have hu : ContDiff ℝ (↑(q+1:ℕ)) u:=(vent K|>.neg.of_le le_top); have hV' : ContDiff ℝ (↑(q+1:ℕ)) V':= hu.exp; have hZ : ContDiff ℝ (↑(q+1:ℕ)) Z:=hp'.mul hV'
    let I' := stallA u j; let I:= stallA F' j; have h₁ : ContDiff ℝ q I := (hp'.fderiv_right (by simp)).clm_apply contDiff_const; have h₂ : ContDiff ℝ q I' := (hu.fderiv_right (by simp)).clm_apply contDiff_const
    have hv'₁: ContDiff ℝ q V':= hV'.of_le (by exact_mod_cast (Nat.le_succ q)); have hhQ: ContDiff ℝ q Z:= hZ.of_le (by exact_mod_cast (Nat.le_succ q)); have hD(v): fderiv ℝ Z v (bolt j)= Z v*I' v+V' v * I v:=by
        have he : DifferentiableAt ℝ F' v:= hp'.differentiable (by simp) v; let X(x:View ι):=u x; have hh:= (hu.differentiable (by simp) v).hasFDerivAt.exp; rw [fderiv_mul he (hV'.differentiable (by simp) v)]; change F' v*fderiv ℝ (fun v:View ι=> Real.exp (u v)) v (bolt j)+V' v*I v= _; rw [hh.fderiv]; change F' v*(V' v*(I' v))+ _ = _; unfold Z; simp only [Pi.mul_apply];ring
    let L':=(l.map (@bolt ι)) 
    have hP(t:List ι)(hp:t.length≤ q) (g:W→ℝ)(hg:ContDiff ℝ (↑(q+1:ℕ)) g) : buoy g x (t++[j])=buoy (stallA g j) x t := by unfold buoy; simp only [List.map_append,List.map_cons,List.map_nil]; rw [fore (q+1) hg.contDiffAt, Lis.takeG (q+1) hg.contDiffAt]; rfl; all_goals rw [List.length_map]; omega
    let v(t:List Bool):=takeout true t l; let w(t:List Bool):=takeout false t l; let α(t):= eval x (µ 0 (V₀ (v t))); let f(t):= Q! (v t) x * buoy u x (w t++[j]); let g'(t):= α t * buoy (Q! []) x (w t++[j]); let W':= Θ x; have ht₀:W'≠0:=(Real.exp_pos _|>.ne')
    have h1: stallA Z j= (fun i=> Z i*I' i+V' i*I i):=funext hD; apply mul_right_cancel₀ ht₀; change Q! (l++[j]) x * W'= (Yarn q f+ Yarn q g')* W'; rw [show Q! _ x*W'= _ from bob A C' D h F T x hf M b K X₀ hM g β hp _, show buoy _ _ _= _ from hP l le_rfl Z hZ,h1]; unfold buoy; change roc (Z*I'+ V'*I) L' _= _; rw [Lis.addedL q L' (Z*I') (V'*I) (hhQ.mul h₂ |>.contDiffAt) (hv'₁.mul h₁ |>.contDiffAt) (by unfold L' q; rw [List.length_map]),add_mul]
    have hz(t:List Bool)(ht:t.length=q) : (w t).length ≤ q:=(sunset false t l ht).trans_le ((part_le ..).trans_eq ht)
    congr 1
    · change buoy (Z*I') x l= _ 
      rw [← Measuring.poker, Lis.paisley q _ _ _ _ hhQ.contDiffAt h₂.contDiffAt le_rfl]; refine stitch q fun t ht=> ?_; change buoy (Q! [] *Θ) x (v t)*buoy I' x (w t)= _; rw [← bob A C' D h F T x hf M b K X₀ hM g β hp,← show buoy _ _ _= buoy I' _ _ from hP _ (hz t ht) _ hu]; unfold f W';ring
    change buoy (V'*I) x l= _; rw [Lis.paisley _ _ _ _ _ hv'₁.contDiffAt h₁.contDiffAt le_rfl,←Measuring.poker]; refine stitch _ fun t ht=>?_ ; change buoy Θ _ (v t)*buoy I _ (w t)=_; rw [← atoms A C' D h F T x hf M b K X₀ hM g β hp, ← show buoy (Q! []) x _ = buoy I x (w t) from hP _ (hz t ht) _ hp']; unfold g' α W'; ring
end YM.MSbar.Duel
