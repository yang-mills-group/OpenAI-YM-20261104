import YM.MSbar.Rolling.Arc
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Rolling
open Matrix MeasureTheory Filter Function Set Next.SectorChange
open Exterior Push Push.Uniform RG Wilson Gauge Lattice Tree Precision Metric
open scoped Topology Classical BigOperators ContDiff
variable {G:Gauge}{E F D:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
open Cacao Bakery Portal Price
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
local notation "µ"=> PowerSeries.coeff
lemma price_move {X:ℝ→D→ Prop}(i:ℝ→D→E)(h:Price X 0 i)(L:E→L[ℝ] F) : Price X 0 (fun x y=> L (i x y)):=by
    obtain ⟨A,h⟩:=h; exact fixed A ‖L‖ (h.mono fun x a i hi=> (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (a i hi) (norm_nonneg _)))
variable {c f:Side}{S: StepData c f}(B: Forest S.ratio)(i:S.Choices)(R T:PathData G)(p q:Clip)(ρ:fieldDir G c 1→ AxisChart G B)
local notation "ol"=>fieldDir G c 1
local notation "X"=> Positions (Primary c G)
local notation "N"=> Positions (Primary f G)
local notation "Y"=> Positions (Key B G)
local notation "Z"=> Positions (Joint B G)
local notation "V"=> Config G f
local notation "K"=> Push.Uniform.block (priced B i p R) 0
local notation "ν"=> center B ρ
variable (J:ChartRatio G)(hJ:LocalRatio J)
variable (n m:ℕ)(A:PowerSeries (Pot (Primary f G))) (F:ℝ → Config G f→ℝ) (u:ℕ)
variable (hc:Serves S G) (hP:Critical B p R ρ) (hQ:ClassicalMatch B p q R T ρ)
variable (ht:Trend F A R p u)
def flame (x:ℝ)(z:Positions (Primary c G) × Positions (Key B G)) : Prop:= yard n x z.1∧ z.2 ∈ den (center B ρ z.1) (Rolling.fuel x ^ m)
noncomputable def peek (z:Positions (Primary c G) × Positions (Key B G)) :Positions (Joint B G) := meetVar z.1 (center B ρ z.1+z.2)
local notation "E₀"=>flame B ρ n m
lemma signing : Price (flame B ρ n m) 0 (fun x z=>peek B ρ z):=by
   refine ⟨max n m,?_⟩; filter_upwards [width] with x ⟨hx,hA,hB⟩ i hi; rw [pow_zero, one_mul]; unfold peek; rw [norm_meet]; exact max_le (hi.1.trans (pow_le_pow_right₀ hB (le_max_left ..))) ((show ‖ν i.1+i.2‖ ≤ _ from hi.2).trans (pow_le_pow_right₀ hB (le_max_right ..)))
include ht hc hP hQ hJ
lemma torch : Price (flame B ρ n m) (u+1) (fun x z=> siteK B i R T p q J F ρ x z.1 z.2 - taste u (picture (peek B ρ z) (barbed B i J A)) x):=by
    have hv:= signing B ρ n m; let Q:= barbed B i J A; let W:=signing B ρ n m
    let v(x:ℝ)(z:X×Y):=peek B ρ z; let I:= pushChart B G i; let H:=singularity I 2; let L:=singularity (swung B J) 0
    have he:Premier (pushChart B G i):=(bornCosts i hc.branches).line (relayB B G)
    have hx:= prop (swung B J) v u hv ((swung_cont B J hJ).of_le le_top)
    have hK:= earn 2 u I he.1 (fun i hi p=>he.zeroP _ _ hi) v hv
    let k:Z→L[ℝ]N := (stamp B G).comp (pushG B); have hk (z): k z=taps B G *ᵥ z:=by unfold taps; rw [LinearMap.toMatrix'_mulVec];rfl
    obtain ⟨M,hM⟩:= price_move v hv k; let μ(x:ℝ)(z:X×Y):= k (peek B ρ z); have hP':∀ᶠ t in Γ,∀ i,E₀ t i → yard M t (μ t i):=by unfold yard; simpa only [pow_zero, one_mul] using hM
    have hU := Price.inherits (ht.tune M) μ hP'; have htQ:=steady B i R T p q ρ hc.branches ht.quiet hP hQ
    refine ((hx.cut hK).nsum hU).egress ?_
    filter_upwards [woodS B i R p J hJ m A F u hc ht] with t h_s z hz
    let a:= siteK B i R T p q J F ρ t z.1 z.2; let x:=z.1; let y:=z.2; let l:= ν x+y; let z':=meetVar x l; let b:Cacao.Pot (Joint B G):= µ 0 L; have h : l= l:=rfl -- collision rename
    have hJ0 : MvPolynomial.eval z' b=0:=by
        unfold b L singularity; rw [PowerSeries.coeff_mk,pots,show (0:ℕ)+0=0 from rfl]; unfold Tensor.diagonal; rw [Tensor.coeff_apply_zero]; unfold swung capitalJ; simp only [map_zero]; rw [show tape (0:Y)=(0:LogArray G B.Free) from rfl,sub_self]
    have hW : MvPolynomial.eval z' (µ 0 H)= Tensor.diagonal (Tensor.coeff (pushChart B G i) 2 0) z':=by unfold H singularity; rw [PowerSeries.coeff_mk, pots]
    have hB:swung B J (t•z')=capitalJ J (t•l):=by unfold swung; rw [map_smul];rfl
    have hφ : a= -(pushChart B G i (t•z')/t^2)+Real.log (F t (postcard G f t (stamp B G l))) + swung B J (t•z') + (dotProduct y (K *ᵥ y))/2+ height c q T x:= by
        unfold a siteK capitalF; rw [hB]; rw [show Real.log (measureK B F t z.1 (kerf t (center B ρ z.1+z.2)))=_ from h_s l hz.2 x] -- h issue
    let t₀(q:PowerSeries (Pot (Joint B G))):=taste u (picture z' q) t; have ht : t₀ (barbed B i J A)= t₀ (splitV L)-t₀ (splitV H)+taste u (picture (stamp B G l) A) t :=by
        let N':=PowerSeries.map (rail (taps B G)).toRingHom A; have hp:z'=z':=rfl; change taste u (picture z' (splitV L -splitV H + N')) t = _
        have hh : t₀ (PowerSeries.map (rail (taps B G)).toRingHom A)=taste u (picture (stamp B G l) A) t:=by unfold t₀; rw [ClearMain,←hk];rfl
        rw [←hh]; unfold t₀ taste picture; unfold N'; simp only [_root_.map_sub,_root_.map_add,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    have ht' : µ 0 L=b:=rfl; have ht₀ : t₀ L=t₀ (splitV L):= by unfold t₀; rw [SplitT L ..,ht',hJ0,add_zero]
    have htH:t₀ H= t₀ (splitV H)+Tensor.diagonal (Tensor.coeff I 2 0) z' := (SplitT H z' t u).trans (by rw [hW])
    change (swung B J (t•z')-t₀ L-(I (t•z')/ _ -t₀ H)+(Real.log (F t (postcard G f t (μ t z)))+ _ -taste u (picture (μ t z) A) t))= a-t₀ _
    rw [ht₀, htH,ht,hφ]; rw [show μ t z=stamp B G l from rfl]; have hx': height f p R (stamp B G l)+Tensor.diagonal (Tensor.coeff I 2 0) z' = height c q T x+dotProduct y (K *ᵥ y)/2:=htQ x y
    unfold I at *; linarith only [hx']
end YM.MSbar.Rolling
