import YM.MSbar.DeltaM.Brawn
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Kelvin
open Function Filter MeasureTheory Cacao PowerSeries Finset Whisk
open scoped Topology BigOperators Classical ContDiff
open Matrix Further.GaussianScalar MvPolynomial Analysis Bakery Lattice
variable {ι σ:Type}[Fintype ι][Fintype σ][DecidableEq ι][DecidableEq σ]
   {n:Side} {l:σ→ Site n}{q: Site n}
    {A : Matrix σ σ ℝ}{B : Matrix ι ι ℝ}
    {p x k:ℕ}{V : View σ→ℝ}{μ ν: View σ}{a b C D W L t Δ ε d:ℝ}
    (u:ι→σ)(h:Injective u)
local notation "ι!"=> imbed u
set_option quotPrecheck false
local notation "w!"=>pinch u A
local notation "f!"=> fieldLaw A⁻¹
local notation "ιρ"=> fieldLaw (pinch u A)⁻¹
local notation "ϑ"=> (f!).prod (fieldLaw (pinch u A)⁻¹)
set_option quotPrecheck false
local notation "U"=> vanish u A
local notation "u!"=> momentum u A
variable (S: Solver u l 0 b C W 0 A)
        (he:∀ i:σ,i∉ Set.range u → x≤ separation (l i) q)
        (hy:0≤ b)
namespace Solver
include h S hy
lemma stamp (j) : (A⁻¹) j j ≤ C:= (le_abs_self _).trans (S.growth.single (show 0 ≤ 0+b from (by linarith only [hy])) j j) -- include hy
local notation "y₀"=>pen μ (1:Matrix σ σ ℝ)
local notation "ν₀"=>pen ν (imbed u)
variable {Z:Finset σ} (hW:∀ i∈Z,Eve b q (l i) ≤ L) (hC: ∀ i,|μ i|≤ a ∧ |ν i|≤ a) (hμ : ∀ i,|μ i-ν i|≤ d* Eve b q (l i))
include he hW hC hμ
lemma pays_cov (hw:FetchD l b ε V) (hv: 0 ≤ a) (hx:1 ≤ L)(hp : 0 ≤ d): let t:=stepW (p+1) C
   let c:=a+t
   let W' := Real.exp (-b*x)*W
   let D:=d+ W'*(C+t)
   Cash (1:Matrix σ σ ℝ) (show Matrix σ σ ℝ from A⁻¹) (imbed u) ((pinch u A)⁻¹) μ ν l V q (L+a+C) D b (ε*(1+p*L)*c^p) p Z := by
     intro t c W' d₀
     let A':=(show Matrix σ σ ℝ from A⁻¹); have hA: A'.PosDef:= S.bids.inv
     let B':= (pinch u A)⁻¹; have ht : (pinch u A).PosDef:= S.bids.submatrix h; have hB:B'.PosDef:=ht.inv
     have hv':0 ≤ C:= S.bsize; have hw':0 ≤ W':= mul_nonneg (Real.exp_pos _|>.le) S.hsize
     have hK:1 ≤ t := le_add_of_nonneg_right (mul_nonneg zero_le_two (Real.exp_pos _|>.le))
     have h₀ : c ≥ 1:= hK.trans (le_add_of_nonneg_left hv); have ht:0 ≤ ε:= hw.nonnegative
     have hp' :0 ≤ t:=zero_le_one.trans hK; have hH:d≤ d₀:= le_add_of_nonneg_right (mul_nonneg hw' (add_nonneg hv' hp'));let L':= L+a+C
     have hd:L≤L':=by unfold L'; linarith only [hv,hv']
     refine ⟨hA,hB,hw.whole,?_, mul_nonneg (mul_nonneg ht (show 0 ≤ (1:ℝ)+↑p*L from ?_)) (pow_nonneg (zero_le_one.trans h₀) _),fun i he=> ?_,fun j T hT heT=> ?_⟩
     · have hG:= realFuel u h S.bids he (a:=0) (B:=b) le_rfl hy S.travels (S.growth.low (show 0 ≤ 0+b by simp [hy])); have hL: C ≤ L':= le_add_of_nonneg_left (add_nonneg (zero_le_one.trans hx) hv);
       have hX : Real.exp (-b*x)*(W*C) ≤ d₀:=by unfold d₀;unfold W' at *; have hg:= mul_nonneg hw' hp';linarith only [hg,hp] -- placeholder
       rw [show (1:Matrix σ σ ℝ)*(A⁻¹)*(1:Matrix σ σ ℝ).transpose=A⁻¹ from (by simp)]
       let Q:= extendM u ((pinch u A)⁻¹)
       refine ⟨le_rfl,hy,hp.trans hH, ?_,?_,?_⟩
       · exact ⟨hv'.trans hL,fun i=> (S.growth.glow i).trans hL,fun i=> (S.growth.forward i).trans hL⟩
       · exact ⟨hv'.trans hL,fun i=>(S.sealed.glow i).trans hL,fun i=> (S.sealed.forward i).trans hL⟩
       exact ⟨hp.trans hH,fun i=>(hG.upper i).trans (mul_le_mul_of_nonneg_left hX (Real.exp_pos _|>.le)),fun i=> (hG.lower i).trans (mul_le_mul_of_nonneg_left hX (Real.exp_pos _|>.le))⟩
     · have he:0≤ L:=zero_le_one.trans hx; positivity
     · have hc:=hC i; have hp': a ≤ L + a + C:= by linarith only [hx,hv']
       exact ⟨hc.1.trans hp',hc.2.trans hp', (hμ i).trans (mul_le_mul hH ((hW i he).trans hd) (Real.exp_pos _|>.le) (hp.trans hH)),(hW i he).trans hd⟩
     let m:=View σ ×View ι; let f(M:m):= momentum u A M; have he':MeasurePreserving Prod.snd ϑ (fieldLaw B'):= measurePreserving_snd; have hd':MeasurePreserving Prod.fst ϑ f! :=  measurePreserving_fst
     have hp₁:= host u h S.bids; let v(M:m):= pen μ (1:Matrix σ σ ℝ) (momentum u A M); let w(M:m):= pen ν (imbed u) M.2
     have hT' (Z : Matrix σ ι ℝ): Measurable (pen ν Z):= (continuous_const.add (toLin' Z).continuous_of_finiteDimensional).measurable
     have hV : Measurable (pen μ (1:Matrix σ σ ℝ)) := (continuous_const.add (toLin' (1:Matrix σ σ ℝ)).continuous_of_finiteDimensional).measurable
     have hf(x): Bank ϑ (p+1) (fun v:m=> v.1 x) t:= (worth hA _ (stamp u h S hy) x (p+1)).move hd'
     have hh(x): Bank ϑ (p+1) (fun y:m=> v y x) c:=by
         have hh : Bank ϑ (p+1) (fun y=>μ x+f y x) (|μ x|+t):=Bank.fest (Bank.cast ..) (Bank.move (worth hA _ (stamp u h S hy) x (p+1)) hp₁); unfold v pen; simp only [one_mulVec,Pi.add_apply]; exact hh.length (add_le_add_left (hC x|>.1) _)
     have hΦ(x): B' x x≤ C:=by
         apply (le_abs_self _).trans; let f:=extendM u B'; have hk: B' x x=f (u x) (u x):= (congr_fun (congr_fun (embeds u h B') x) x).symm; rw [hk]; exact S.sealed.single (show 0≤0+b by rw [zero_add]; exact hy) _ _
     have hj(x): Bank ϑ (p+1) (fun y:m=> w y x) c:=by
         have ht : Bank ϑ (p+1) (fun y:m=> (ι! *ᵥ y.2) x) t:=by
             by_cases he:x∈ Set.range u
             · obtain ⟨j,rfl⟩:=he; simp_rw [show ∀ v:View ι,(ι! *ᵥ v) (u j)=v j from fun v=> congr_fun (shares u h v) j]; exact (worth hB C hΦ j (p+1)).move he'
             simp_rw [fun (q: View ι)=> inactive u x he q]; refine (Bank.cast ..).length (by simpa)
         have ht': Bank ϑ (p+1) (fun y:m=> w y x) (|ν x|+t):= Bank.fest (Bank.cast ..) ht
         exact ht'.length (add_le_add_left (hC x|>.2) _)
     have hs(i:σ): Bank ϑ (p+1) (fun y:m=> v y i-w y i) (d₀*Eve b q (l i)):=by
         have ht(y:m):v y i-w y i = μ i-ν i+ ∑ j:σ,(vanish u A) i j* y.1 j:=by
              unfold v w pen momentum; simp only [one_mulVec,Pi.add_apply]; change _ + (_+(imbed u*ᵥy.2) i)-_= μ i-ν i+ ((vanish u A)*ᵥy.1) i; abel
         simp_rw [ht]; letI : MeasurableSpace σ:= ⊥; have Hx := (Bank.cast (μ:=ϑ) (μ i-ν i) (p+1)).length (hμ i)
         have hc: Bank ϑ (p+1) (fun y:m=> μ i-ν i+ ∑ j:σ,vanish u A i j*y.1 j) (d*Eve b q (l i)+( (∑ j:σ,|vanish u A i j|)*t)):=by rw [Finset.sum_mul]; exact Bank.fest Hx (Bank.mcast _ _ _ fun j _=> (hf j).falls _)
         have he := vanSmall u h S.bids he hy S.travels i; simp only [liftW,zero_mul,Real.exp_zero, pow_zero,mul_one] at he; apply hc.length; apply le_trans (add_le_add_right (mul_le_mul_of_nonneg_right he hp') _); apply le_trans _ (mul_le_mul_of_nonneg_right (show d+W'*t ≤ d₀ from ?_) (show 0 ≤ Eve b q (l i) from (Real.exp_pos _).le)) -- fill
         · unfold W';exact le_of_eq (by ring)
         unfold d₀; exact add_le_add_right (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hv') hw') _
     obtain ⟨hv',ht',hf'⟩:= FetchD.solar hw hs hW j (hp.trans hH) hy (zero_le_one.trans hx) (hV.comp hp₁.measurable) ((hT' _).comp he'.measurable) (fun j _=> hh j) (fun j _=> hj j) h₀ T hT heT
     have hG : ε*c^p ≤ ε*(1+(p:ℝ)*L)*c^p:=by
           have hh : 1≤1+(p:ℝ)*L:= le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hx)); exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right ht hh) (pow_nonneg (zero_le_one.trans h₀) _)
     let g(x):= glance V [j] x * eval x (play T); have hu : Measurable g:= ((curtain j hw.whole).measurable.mul (vent (play T)|>.continuous.measurable))
     rw [show pillar (1:Matrix σ σ ℝ) μ j V (play T) A'=(∫ i, g (v i)∂ϑ) from ?_,show pillar (imbed u) ν j V (play T) B'=(∫ i,g (w i)∂ϑ) from ?_]; · exact ⟨hv'.trans hG,ht'.trans hG,hf'.trans_eq (by ring)⟩
     swap
     · change (∫ i,g (y₀ i) ∂f!)= _; nth_rw 1 [← hp₁.map_eq]; exact integral_map (μ:=ϑ) hp₁.measurable.aemeasurable (hu.comp hV|>.aestronglyMeasurable)
     change (∫ i,g ((ν₀) i) ∂fieldLaw B') = _; nth_rw 1 [← he'.map_eq]; exact integral_map (μ:=ϑ) he'.measurable.aemeasurable (hu.comp (hT' (imbed u))|>.aestronglyMeasurable)
end Solver
end YM.MSbar.Kelvin
