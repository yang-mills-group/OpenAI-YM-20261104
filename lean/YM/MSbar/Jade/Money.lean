import YM.MSbar.Jade.Cabot
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
lemma fares (h₀:flags R.p.threshold (chambers F Y J W ν (D! x))=∅)(h₁:flags R.p.threshold (chambers F Y J W ν (D! u))= ∅) : (F! x-F! u) - (taste p (picture (meetVar Z (A! x)) (barbed F v χ H')) t - taste p (picture (meetVar Z (A! u)) (barbed F v χ H')) t)=
     (Real.log (R.eval (postcard G f t (P! x))) - Real.log (R.eval (postcard G f t (P! u))) - (ore R H' t p (P! x)-ore R H' t p (P! u)))
      +(-R.beta*φ (t • (meetVar Z (A! x))) - (- R.beta *φ (t • (meetVar Z (A! u))))+ (taste p (picture (meetVar Z (A! x)) (singularity φ 2)) t-taste p (picture (meetVar Z (A! u)) (singularity φ 2)) t))
      +(θ (t • (meetVar Z (A! x)))-θ (t • (meetVar Z (A! u))) -(taste p (picture (meetVar Z (A! x)) (singularity θ 0)) t-taste p (picture (meetVar Z (A! u)) (singularity θ 0)) t)) :=by
    let T₁:=λ i:X₀=>P! i; let i'(z):= L! z; let G₀:= (mold R F v); let k':=pinch Λ H; let C':Matrix (Lake F X G) (Lake F X G) ℝ:= k'⁻¹; let N:=singularity φ 2; let J':=singularity θ 0; let g(x:X₀):=Real.log (Next.SectorChange.pay χ (tape ((c! ∘ includeX F X)+t •x : X₀))); let A':=taps F G; let M:= PowerSeries.map (Rolling.rail A').toRingHom H'
    let p'(x:X₀)(q:PowerSeries (Pot (Joint F G))):=taste p (picture (L! x) q) t; have hp(x:X₀) : p' x (barbed F v χ H')= p' x (splitV J') - p' x (splitV N)+p' x M:=by unfold p' M taste picture barbed; simp only [map_add,map_sub,Finset.sum_sub_distrib,mul_sub,mul_add,Finset.sum_add_distrib, Finset.sum_sub_distrib];rfl -- syntax
    have hz(x:X₀) (hk:x∈S!) (hi:flags R.p.threshold (Q₀ (D! x))=∅):F! x=(Real.log (R.eval (postcard G f t (P! x))) -(R.beta* φ (t • (L! x)))) + g x+ dotProduct x (k'*ᵥx)/2:=by
         have he:Q₀ (D! x)=postcard G f t (P! x):= applies F R v J χ X Y U' t Z h ht x hU hk
         let pT:= t • meetVar Z (A! x)
         have hu: pushChart F G v pT=noiseTaylor S W (Q₀ (D! x)) v:=by
             rw [he]; unfold pushChart; change noiseTaylor S (represent (relayB F G pT).1) (represent (relayB F G pT).2) _= _
             unfold pT; rw [map_smul, Prod.smul_fst,Prod.smul_snd]; unfold postcard; rw [map_smul,map_smul];rfl
         have hW: R.exponent (Q₀ (D! x)) = Real.log (R.eval (postcard G f t (P! x))):=by rw [←he, RG.Rep.eval,Activities.gas_one _ _ hi,mul_one,Real.log_exp]
         change fLog _ _ _ _ _ _ _ _ C'= _; rw [fLog, show C'⁻¹=k' from nonsing_inv_nonsing_inv k' (isUnit_iff_ne_zero.mpr ((h.positivity.submatrix (secureY F X G)).det_pos.ne')), rental,hW,hu]; -- eq args
    have hxₓ(x:X₀) :p' x M= taste p (picture (P! x) H') t:=by unfold p' M; rw [ClearMain]; unfold A' taps; rw [LinearMap.toMatrix'_mulVec];rfl
    let k:= k'; have hj(x:X₀): p' x (splitV N)= p' x N- MvPolynomial.eval (L! x) (potter (pushChart F G v) 2):=by apply eq_sub_of_add_eq; unfold p'; rw [SplitT N, show PowerSeries.coeff 0 N=potter _ 2 from ?_]; unfold N singularity;rw [PowerSeries.coeff_mk]
    let S':=taste p (picture (L! x) J') t; have hk(S:X₀):p' S (splitV J') = p' S J'- θ (0:T):=by apply eq_sub_of_add_eq; unfold p'; rw [SplitT J']; congr 1; unfold J' singularity; rw [PowerSeries.coeff_mk,pots]; exact (Tensor.coeff_apply_zero ..).symm -- location symmetric
    have hL:= Jade.appeal F R v J X Y U' t Z e l ρ ha hh.quiet hG hT h.positivity ht x u; have he(v:Positions (Primary f G)):ore R H' t p v=taste p (picture v H') t- height f R.clip R.path v:=by rw [← Wave.tariff_data p R.clip R.path H' hh]; unfold taste picture ore; refine Finset.sum_congr rfl fun i _=>?_ ; rw [PowerSeries.coeff_map];rfl
    let j(x:X₀):= T₁ x; have hd:g x-g u= θ (t•(L! x))-θ (t•(L! u)):=roseP F R v J χ X Y U' t Z h ht u x hU hX hχ hg hx hx'
    change F! x-F! u- (p' x _-p' u _)= _ ; rw [hz x hx h₀,hz u hx' h₁,hp,hp,hj,hj,hk,hk,hxₓ,hxₓ,he,he];
    dsimp only at hL; unfold p' J' N; unfold k'
    linarith only [hL,hd]
end YM.MSbar.Jade
