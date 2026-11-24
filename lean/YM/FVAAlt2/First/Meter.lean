import YM.FVAAlt2.First.Impress
/-! # Connected scalar diagnostic.Pl use exact material. Output does not require field map
 between test systems; proof directly on Peal.together.Power.Pos. Supply truth. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.First.Clockers
open Function Set Filter Finset Topology Lattice MeasureTheory
open Precision Extra.FD Maxwell Labels Extraction Matrix
open FormalOPE FormalOPE.RG10.Gazebo FormalOPE.RG10.Position FormalOPE.RG10.Carryon
open Pert Pert.Position PertExtension PertExtension.LatticePT PertExtension.Position PertExtension.Physical
open Home Home.Subsidy Tent SchemeConversionRG11 Portray
open scoped BigOperators Classical Topology PowerSeries Matrix
open RG10 (Through)
open Pert.Triangle

open PertExtension.Position.Triangle (fps)
open PowerSeries (C coeff constantCoeff)
variable {G:Gauge}{F:Frames G}{d n m:ℕ}
local notation "V"=> RG10.Position.Deck F 6
local notation "K"=> deck F 6
local notation "E"=> Pert.Position.E F 6
local notation "Ω"=> constantCoeff (R:=ℝ)
local notation "PropW"=> Fin 3
variable (B:Issue F 6) (T:Fin m ↪ Fin 3) (U: ℕ→Buffer F 6)
lemma touch_budget (i:ℕ): coeff i ( RG10.Position.Peal.touch F (loot B) T)= ( B m ( RG10.Position.Peal.near T ) i (basic F ∘ T) ).re:= by
 unfold RG10.Position.Peal.touch; simp_rw [map_sum,PowerSeries.coeff_C_mul,loot,PowerSeries.coeff_mk]
 let H:=B m (RG10.Position.Peal.near T) i
 let f(j:Fin m)(k:V):= RG10.Position.Peal.tune F (T j) k
 let lp(j:Fin m):= basic F (T j)
 have ht(j:Fin m): lp j=∑ k:V,(f j k :ℝ) • K k:= by
    simp_rw [ RCLike.real_smul_eq_coe_smul («K»:=ℂ) ]; change lp _=∑ k:V, ( ↑(f j k):ℂ) • K k; simp_rw [ f, RG10.Position.Peal.contour ]; exact ((K).sum_repr _).symm
 rw [show (basic F ∘ ⇑T)= _ from funext ht]; change _=( H.toMultilinearMap _ ).re; rw [MultilinearMap.map_sum, Complex.re_sum]; apply Finset.sum_congr rfl; intro v _; rw [ MultilinearMap.map_smul_univ, Complex.smul_re ];rfl
lemma peal_lit : RG10.Position.Peal.near ( Function.Embedding.refl (Fin 3) ) = profileChoice := by ext1 i; exact Eq.symm ( RG10.Position.Peal.factor i )
variable (hg:G.Simple)(hh:B.Twist)
include hh
lemma one_lit (i: Fin 3): constantCoeff ( RG10.Position.Peal.touch F (loot B) ( RG10.Position.Peal.single i ) )=0:= by
 rw [ ← PowerSeries.coeff_zero_eq_constantCoeff_apply,touch_budget, hh, show (basic F ∘ ⇑( RG10.Position.Peal.single i )) = ( fun _ :Fin 1=> basic F i ) from rfl,Coupling.kill_single, Complex.zero_re ]
include hg
lemma pair_lit (i: Fin 3): constantCoeff ( RG10.Position.Peal.touch F (loot B) ( Fin.succAboveEmb i ) )=0:= by
 rw [ ← PowerSeries.coeff_zero_eq_constantCoeff_apply,touch_budget,hh ]
 have hz : i=0 ∨ i=1 ∨ i=2:=by omega
 rcases hz with rfl | rfl | rfl
 · rw [show basic F ∘ ⇑( Fin.succAboveEmb 0 )=( ![basic F 1,basic F 2] ) from ?_, Coupling.kill_even_pair ]; rfl
   funext j; fin_cases j <;> (apply congr_arg (basic F); decide)
 · rw [ show basic F ∘ ⇑( Fin.succAboveEmb 1 )=( ![basic F 0,basic F 2] ) from ?_, Coupling.kill_odd_pair hg _ (by decide) ]; rfl
   funext j; fin_cases j <;> (apply congr_arg (basic F); decide)
 rw [ show basic F ∘ ⇑( Fin.succAboveEmb 2 )=( ![basic F 0,basic F 1] ) from ?_, Coupling.kill_odd_pair hg _ (by decide) ]; rfl
 funext j; fin_cases j <;> (apply congr_arg (basic F); decide)
lemma together_b : coeff 1 ( RG10.Position.Peal.together F (loot B))= ( B 3 profileChoice 1 (basic F)).re :=by
 unfold RG10.Position.Peal.together; rw [map_add,map_sub,map_sum]; have hτ(i:Fin 3): coeff 1 ( RG10.Position.Peal.touch F (loot B) ( Fin.succAboveEmb i ) * RG10.Position.Peal.touch F (loot B) ( RG10.Position.Peal.single i ) )=0:=by rw [ PowerSeries.coeff_one_mul, pair_lit B hg hh,one_lit B hh,mul_zero,mul_zero,zero_add]
 let A(i:Fin 3):=RG10.Position.Peal.touch F (loot B) ( RG10.Position.Peal.single i )
 have Hp: coeff 1 ((2:fps)*∏ i:Fin 3,A i)=0:=by simp_rw [ Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one, PowerSeries.coeff_one_mul, map_mul,A,one_lit B hh ]; simp
 simp_rw [hτ]; rw [ show coeff 1 ((2:fps)*∏ i:Fin 3,RG10.Position.Peal.touch F (loot B) ( RG10.Position.Peal.single i ))=0 from Hp, Finset.sum_const_zero,sub_zero,add_zero,touch_budget,peal_lit ];rfl

lemma imprint_lit (h: U 0=0): coeff 1 ( RG10.Position.Peal.together F (loot (Issue.imprint U B)))= ( B 3 profileChoice 1 (basic F)).re:=by
 rw [ together_b (Issue.imprint U B) hg (Issue.aims hh h) ]; unfold Issue.imprint; rw [Tape.leading _ _ h, _root_.add_apply, Tape.vary_at, hh 3,  Finset.sum_eq_zero (f:=fun i=> SchemeConversionRG11.Issue.gaussian F 6 profileChoice (update (basic F) i ((U 1).val (basic F i)))) (fun i _=> (finiteTest hg F).detectorIndependent ( U 1 ) i), zero_add ]
end YM.FVAAlt2.First.Clockers
