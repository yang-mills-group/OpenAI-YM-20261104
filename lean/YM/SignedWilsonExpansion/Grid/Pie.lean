import YM.SignedWilsonExpansion.Grid.Gyro
import YM.SignedWilsonExpansion.Grid.Statement
namespace YM.SignedWilsonExpansion.Overlap.Chart
/-! # Signed independent phase derivative for arbitrary bearers of magnetic test ea₁₂. Corners trade. -/
set_option autoImplicit false
noncomputable section
open Function Filter Set MeasureTheory Finset Maxwell Maxwell.Free Maxwell.Wick
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus FVA2.Position FVA2.Arrival
open MS MS.Native MS.Local.Physical MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Fleet MS.Theater MS.Land
open Dframe Scale Scale.Facets Scale.Equator Scale.Level Scale.Meter Reg.Token
open WickFace PhaseTilt Contrast AxialBill PairWave Marque Mirror
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {O:Booked (Press.portDeck G)}(M:MS_Data G O)(Y:Initialize G){V:Normalize.Store G}(K: Rose.Pick V)
variable (S:Land.Prescription (Press.portDeck G))(h:G.Simple)(hs:TaylorOKF M (Press.wickInput Y) S)(hr:Favors.Horder S)(hu: Ace.UnitP S)
local notation "p" => Mirror.site
local notation "E" => sl G
local notation "Ω" => ( Normalize.leaf G 4 )
local notation "ψ" => Mirror.seats
local notation "N" => Mirror.amount G
variable (v:Sec G 4)(a b:Idx)(i j:Fin 2)(ht:i≠j)
def dual : (Sec G 4)→ₗ[ℂ] ℂ:= dyad Mirror.site i j (wmark G a a) ∘ₗ coeS 4
include h ht
lemma value (k: Sec G 4) : dual a i j k= ψ a k*N:= by
     rw [mul_comm]; refine WickFace.at_low h (dual a i j) ( N • ψ a ) ?_ ?_ k
     · rw [dual,LinearMap.comp_apply, show coeS 4 Ω= 1 from rfl,dropI p _ i j ht,WickFace.single_off,LinearMap.smul_apply,Mirror.heel,smul_zero ]
     intro u v; unfold dual; rw [LinearMap.comp_apply,show coeS 4 (glow G u v)=wmark G u v from rfl,Marque.dyAt p i j ht serves, LinearMap.smul_apply, fares h, Mirror.amount,AxialBill.Epair p serves ]; have H : pay p i j=pay p 0 1:= by fin_cases i <;> fin_cases j <;> (first| rfl| exact (ht rfl).elim| exact pay_m ..)
     rw [H,smul_eq_mul]; push_cast; rfl
omit ht
lemma self_due (z:Sec G 4) : pairField p z =2* ψ 3 z*N:= by unfold pairField; rw [LinearMap.add_apply]; change dual 3 0 1 z+ dual 3 1 0 z=_; rw [value h 3 0 1 (by decide), value h 3 1 0 (by decide) ]; ring
local notation "W" => Statement.address2 G true false
lemma opp_due (A:FieldEnd G 4): Manifest.response p (W) A=( ψ 3 (A ( E 1 ))+ ψ 1 (A ( E 3 )) )*N:= by
     unfold Manifest.response; rw [LinearMap.coe_mk,AddHom.coe_mk, Fin.sum_univ_two ]; apply Eq.trans (show iris p (update W 0 (A (W 0)))+iris p (update W 1 (A (W 1)))= dual 1 0 1 (A ( E 3 )) + dual 3 1 0 (A ( E 1 )) from congrArg₂ _ ?_ ?_) 
     all_goals first| (apply congr_arg (moment G (p).val); funext i; fin_cases i <;> rfl)| ( rw [value h 1 0 1 (by decide), value h 3 1 0 (by decide) ]; ring )
local notation "X" => Xi G
local notation "B" => GroupS.gaugeM Y K M
local notation "Ξ" => PowerSeries.coeff
variable (x:Stage 3) (ν:ℝ)
local notation "T" => (Ξ 2 (B ν (-1) 4))
include hs hr hu
lemma invoice : T∈Normalize.Change G 4:= ( (Scale.Precise.mainM ν Y K M S h hs hr hu).paid (-1) 4 ).high 2 (by decide)
-- same-edge scale α already established independently. Use charge and cancel pair denominator.
def main (G:Gauge):ℝ:= G.casimir/(48*Real.pi^2)
def offtrack (G:Gauge):ℝ:=-( G.casimir/(8*Real.pi^2) )
lemma payment : ψ 3 (T ( E 3 ))=( main G:ℂ ):= by
    obtain hh:= AxialBill.chargeP M Y K S h hs hr hu ν p serves; rw [ self_due h ] at hh; have ht (z:ℂ) : -( ( 2:ℝ )*( OrderHigh.kinetic G+OrderHigh.locus G ) ) • z= (2* ( main G:ℂ )) * z:= by unfold main OrderHigh.kinetic OrderHigh.locus; rw [ FVA2.Lambda.Gaussian.b0 ]; simp only [Complex.real_smul]; push_cast; ring
    rw [ht] at hh; exact mul_left_cancel₀ (by norm_num : (2:ℂ)≠0) (mul_right_cancel₀ ( Mirror.cost_ne h ) hh)
-- overlap scale exposed by two distinct paired projections; not angular extrapolation at ε. sign.
lemma tipping : ψ 1 (T ( E 3 ))=( offtrack G:ℂ ):= by
    obtain hh:= Statement.tariff M ν true p S Y h hs K hr hu serves; rw [show (!true)=false from rfl,opp_due h, show ψ 3 (T ( E 1 ))= ψ 1 (T ( E 3 )) from (Mirror.trade h T ( invoice M Y K S h hs hr hu ν ) 1 3 3 1 1 (by decide) (by decide)) ] at hh; rw [← two_mul] at hh
    have ht (z:ℂ) : -( ( 2:ℝ )*Align.salaryQ G ) • z= (2*(offtrack G:ℂ))*z:= by unfold offtrack Align.salaryQ; rw [FVA2.Lambda.Gaussian.b0 ]; simp only [Complex.real_smul]; push_cast; ring
    rw [ ht ] at hh; exact mul_left_cancel₀ (by norm_num : (2:ℂ)≠0) ( mul_right_cancel₀ ( Mirror.cost_ne h ) hh )
def overlaps : Finset Idx:= {0,1,4,5}
lemma gratuity (hh:a∈overlaps): ψ a ( T ( E 3 ) )=(offtrack G:ℂ):= by
    obtain ⟨b,hu'⟩:= (by decide :∀ a∈overlaps,∃ b:Fin 10,Normalize.twin (Normalize.table b) 1 a ∧ Normalize.twin (Normalize.table b) 3 3 ) a hh; rw [Mirror.trade h T (invoice M Y K S h hs hr hu ν) 1 a 3 3 b hu'.1 hu'.2,tipping M Y K S h hs hr hu ]
def priceR (G:Gauge)(x:Stage 3):ℝ:= main G*Marque.actual G x 3+∑ a∈overlaps,offtrack G*Marque.actual G x a
lemma listed : X x (T ( E 3 ))= (priceR G x:ℂ):= by
   rw [ Mirror.orders h T (invoice M Y K S h hs hr hu ν) 3,map_add,map_sum,map_smul, Contrast.bell_unit, smul_zero,zero_add ]; simp_rw [map_smul]; unfold priceR; push_cast; rw [ show ( Finset.univ: Finset Idx )=insert 2 (insert 3 overlaps) from by decide ]; rw [sum_insert (by decide),sum_insert (by decide),Marque.Xi_actual x 2, Marque.void_w,Marque.Xi_actual x 3, payment M Y K S h hs hr hu ]; simp only [ Complex.ofReal_zero, mul_zero,zero_add,smul_eq_mul ]; congr 1; apply Finset.sum_congr rfl; intro i hi; rw [ gratuity M Y K S h hs hr hu i ν hi, Marque.Xi_actual x i ] -- abbr sl definitional
end
end YM.SignedWilsonExpansion.Overlap.Chart
