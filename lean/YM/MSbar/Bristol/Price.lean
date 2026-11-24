import YM.MSbar.Bristol.Range
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bristol
open Function Filter Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film Lodge Measuring RawP
variable {G:Gauge}{c:Side}{σ:Type}[Fintype σ][DecidableEq σ]
variable {G:Gauge}{c:Side}{p q m:ℕ} (R:Rep G c)(Z:Nesting G c)(b:PowerSeries ℝ)
local notation "X₀"=>Positions (Primary c G)
local notation "X"=> Pot (Primary c G)
local notation "Ω"=>ink c R.clip R.path
local notation "V"=> PowerSeries ℝ
local notation "φ"=>film R Z
local notation "S"=> bley b Z Ω
variable (u r s:ℝ)
local notation "μ"=>PowerSeries.coeff
local notation "ℓ"=> Measuring.chart c G
variable (i:G.ColorIndex){A w v t x a y Y E D:ℝ}{k d:ℕ}
open JetTab
local notation "x!"=> sun G i
variable (Z':Positions (Primary c G)→ℝ)
lemma cashH (h:ContDiffAt ℝ 2 Z' 0)(hv:JetTab (Measuring.chart c G) a q v {0} Z' 1 A)(hp:2 ≤ q)(ha:0≤ a)(hr:0<v) : |stackH c (sun G i) (rim Z')| ≤ A/v^2:=by
     let f:= ∑ i∈range 3,potter Z' i; have hh:clue f=blockTaylor 2 Z' :=_root_.funext (fun v=>by unfold clue f blockTaylor; rw [_root_.map_sum,Finset.sum_apply]; exact sum_congr rfl fun i _=>pots Z' v i)
     have he:= ((blockTaylor_jets h 2 le_rfl)); have hp'(L:List (Primary c G))(hy:L.length=2): buoy (clue f) 0 L=buoy Z' 0 L:= by
           rw [CrossH.chain _ L 2 0 ((helm ..).contDiffAt) (by omega),CrossH.chain Z' L 2 0 (by exact h) (by omega)]; have hz: iteratedFDeriv ℝ L.length (clue f) 0= iteratedFDeriv ℝ L.length Z' 0:=by rw [hy,hh]; exact he
           rw [hz]
     have hZ : rim Z'=rim (clue f):=by rw [hh]; ext1 x; ext1 y; exact (iteratedFDeriv_two_apply Z' 0 ![x,y]|>.symm).trans ((congr_arg (fun v:Tensor.T _ ℝ 2=> v ![x,y]) he.symm).trans (iteratedFDeriv_two_apply ..))
     rw [hZ]; apply (Bronze.quant i f ha _ hp); intro i; rw [←CrossH.scored]; refine le_trans (le_of_eq ?_) (JetTab.count hv hr 0 (Set.mem_singleton _) i); apply Whisk.stitch; intro L hL; rw [hp' (i::L) (by simp [hL])]
lemma gatherH (f g:X₀→ℝ)(hp:ContDiffAt ℝ 2 f 0)(hg:ContDiffAt ℝ 2 g 0) : rim (f+g)=rim f+rim g:=by
     ext1 i;ext1 j; have he:= iteratedFDeriv_add_apply (i:=2) hp hg; exact (iteratedFDeriv_two_apply (f+g) 0 ![i,j]).symm.trans (by rw [he,_root_.add_apply,iteratedFDeriv_two_apply,iteratedFDeriv_two_apply]; rfl); -- fill
lemma realH (a:ℝ)(f:X₀→ℝ)(hp:ContDiffAt ℝ 2 f 0) : rim (a • f)=a • rim f:=by
     ext1 i;ext1 j; have he:= iteratedFDeriv_const_smul_apply (i:=2) (a:=a) hp; rw [show rim (a • f) i j= _ from (iteratedFDeriv_two_apply (a • f) 0 ![i,j]).symm]; rw [he,_root_.smul_apply,iteratedFDeriv_two_apply];rfl
local notation "λ'"=> surf b s u p
local notation "T"=> film R (bley b Z (ink c R.clip R.path)) s p
local notation "f!"=> film R Z r p
local notation "P"=> pegs Z b s u p
local notation "g'"=> f! ∘ (Yturn u) -- Coe def.
-- projection pricing
variable (hv:0<u) (hu:u*r=s) (hs:0 < w) (hR:Premier (Rolling.main c R.clip R.path)) (h:Kind Z)(hx:Expanse Z 1 p)(hf:ContDiffAt ℝ 2 (film R Z r p ∘ (Yturn u)) 0)
variable (hK: JetTab (Measuring.chart c G) a q w {0} (film R Z r p ∘ Yturn u) 1 y)
variable (hΩ:1 ≤ |caliper c (sun G i) (ink c R.clip R.path)|)(he:|stackH c (sun G i) (rim (film R (bley b Z (ink c R.clip R.path)) s p))| ≤ A)(ha:0≤a)(hq:2 ≤ q)
local notation "Γ"=> stackH c (sun G i)
include hv hu hs hR h hx hf hK hΩ he ha hq
lemma rentH (hp:Tin (Measuring.chart c G) a q m w (pegs Z b s u p) t)(hl:1 ≤ m) : |surf b s u p|≤ A+y/w^2+t/w^2:=by
     have hb: stackH c x! (rim (T))= Γ (rim (g'))+ caliper c x! P + surf b s u p*caliper c x! (ink c R.clip R.path):=by
         let S':= T; let Q:= pegs Z b s u p; let f:= clue Q; let K:=surf b s u p; let g:=f!∘ (Yturn u); let D:=clue (ink c R.clip R.path); have he : s/u=r:= div_eq_iff hv.ne'|>.mpr (hu.symm.trans (mul_comm ..)); have hF: ContDiffAt ℝ 2 f 0:=(helm ..).contDiffAt;have hG: ContDiffAt ℝ 2 (clue (ink c R.clip R.path)) 0:= (helm ..).contDiffAt
         change Γ (rim S') = _; rw [show S'=g+f+K • D from slips R Z b u r s he hv hu h hx hR, gatherH (g+f) _ (show ContDiffAt ℝ 2 (g+f) 0 from hf.add hF) (show ContDiffAt ℝ 2 (K • D) 0 from hG.const_smul K),gatherH g f hf hF,realH K D hG, show Γ (_+_)= _ from (_root_.map_add Γ _ _),show Γ (_+_)=_ from (_root_.map_add Γ _ _), show Γ (_ • _)=_ from (_root_.map_smul Γ K (rim D))]; rfl
     rw [hb] at he; apply le_trans (le_mul_of_one_le_right (abs_nonneg _) hΩ); rw [← abs_mul]
     apply le_trans (abs_le.mpr ⟨?_,?_⟩)
     · rfl
     · have hv':= cashH i _ hf hK hq ha hs; have hz := Bronze.quant i (pegs Z b s u p) ha (fun i=>hp.fan 1 hl i) hq; linarith only [(abs_le.mp he).1,(abs_le.mp hv').2,(abs_le.mp hz).2] -- .
     have hv':= cashH i _ hf hK hq ha hs; have hz := Bronze.quant i (pegs Z b s u p) ha (fun i=>hp.fan 1 hl i) hq; linarith only [(abs_le.mp he).2,(abs_le.mp hv').1,(abs_le.mp hz).1]
end YM.MSbar.Bristol
