import YM.MSbar.Sat.Brave
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory Metric
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{U:Config G f}{R:Rep G f}{σ C T a v y δ w D b u Δ μ ψ t₀:ℝ}{k n:ℕ}
open Finset YM.MSbar.Bulk SectorNext.Vacuum Precision Tree Pressure Pressure.Stores Push.Uniform
variable (F : Forest S.ratio)(J: Voice G)(p:Palisade)
     (i:S.Choices) (j:Key F G) (t:ℝ)(m:ℕ)
set_option quotPrecheck false
local notation "N"=> (Key F G)
local notation "H"=> priced F i R.clip R.path
local notation "L"=> address F G
local notation "X"=> shutterPad F G j m
local notation "x₀"=> crown F i j t m R
local notation "h!"=> pedal F x₀
local notation "k₀"=> ice p.coords p.gap p.a p.density
variable (x:Positions (Primary c G))(h:Grants i R F p n)(g:Clear G J) (hd: S.patch.Branches S.kernel G)
local notation "T!"=> R.p.threshold
local notation "V"=> represent (tint G _ x)
local notation "Y"=>halo (2*k) X
local notation "τ"=> excavation F Y T! b
variable (hA : Floss p J t u D t₀ v b a Δ ψ m)
    (htb: necklace S.patch≤k) (hv: represent (tint G (Exterior.Body 1 c) x) ∈ calm G c v) -- notation quote fails
    (hx: ‖x‖ ≤ a)(hb: bonfire F G (halo (2*k) (shutterPad F G j m)) (J.C*D) u≤ t₀)
variable {cF : ℝ} (hu:U∈excavation F (halo (2*k) (shutterPad F G j m)) R.p.threshold b)
set_option quotPrecheck false
local notation "W"=> chink F J V U Y
local notation "W'"=> chink F J V (pedal F (crown F i j t m R) U) Y
local notation "U!"=> exterior F J V U Y
local notation "V!"=> exterior F J V (pedal F (crown F i j t m R) U) Y
-- all pre V and witness.This regulator for weighted.A.Duty
variable (ρ:ℝ) (hy:Quasi R.eval ρ) (sold:Admitted (represent (tint G (Exterior.Body 1 c) x)) R S σ C δ T w)(hz:0≤ R.beta) -- Amb notation
open WilsonStartup
local notation "Q!" => hurry p (max a D) Δ ψ
local notation "A!" => outset R.p σ C δ T R.beta k (X).card
local notation "C!"=> Real.exp (ρ*(J.C*u)*(4*↑(X).card)+R.beta*(Δ*p.noise))
variable (hP:Psalm S R cF y)(L0:MergeProof.Menu.Arsenal R)
local notation "M"=> tailsSet F J i j t x R
local notation "p!"=> chance S R V
include F k g
variable (hK:2 ≤ k)(hw:R.p.B≤ k)(hQ : Decent R.clip R.p)(hc:Continuous R.eval)(hρ:∀ μ,0< R.eval μ)
variable (hs: flags cF (represent (tint G (Exterior.Body 1 c) x))=∅)(hq:0≤ y) {q u':ℝ}
include sold hz hd h hP L0 hy hA hv hs hq hK hw hc hρ hb htb hx hQ

lemma lap (ha:p! (excavation (G:=G) F Y R.p.threshold b)ᶜ≤ q)
    (N':ℕ) {r A B :ℝ}(hr:r ≤ 0)(hp0:u'+(N':ℝ)*(|t| *Δ) ≤ A)
    (hΔ:0≤Δ)
    (he: A!+R.beta*(Q! -u')≤ r)(ht:(1+C!)*q+y*(R.p.mass (youth F Y) 2*Real.exp ((youth F Y).card*w)) ≤ B)
    (hv0:0≤B): p! (M A) ≤ Real.exp (r*N') + ↑N'*B:=by
   have hm i':MeasurableSet (M i'):= (fees (k:=k) F J i j t m x g i').from_here
   let v n:ℝ:= u'+(n:ℕ)*(|t| *Δ)
   have h₀(n:ℕ) : p! (M (v n)) ≤ Real.exp (r*n)+ ↑n*B:=by
       induction n with
       | zero=> simpa only [Nat.cast_zero,mul_zero,zero_mul,Real.exp_zero,add_zero] using chance_g sold (hm (v 0))
       | succ n ih=>
         have hℓ:= sheared (u':=v (n+1)) F J p i j t m x h g hd hA htb hv hx hb ρ hy sold hz hP L0 hK hw hQ hc hρ hs hq ha
         let w n:= p! (M (v n)); let P:=Real.exp r; have hr': P ≤1:=Real.exp_le_one_iff.mpr hr
         have hx' : u'≤ v (n+1):=le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (abs_nonneg _) hΔ))
         rw [show v (n+1)-_=v n from (by unfold v; push_cast; ring)] at hℓ; have hκ: w (n+1) ≤ P*w n+B:= hℓ.trans (add_le_add (mul_le_mul_of_nonneg_right (Real.exp_monotone (le_trans (add_le_add_right (mul_le_mul_of_nonneg_left (sub_le_sub_left hx' _) hz) _) he)) (chance_pos sold (hm (v n)))) ht)
         refine hκ.trans ((add_le_add_left (mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le) B).trans ?_)
         rw [mul_add]; push_cast; rw [mul_add r,mul_one,add_comm (r*(n:ℝ)),Real.exp_add]; have he:= mul_le_of_le_one_left (show 0 ≤ (n:ℝ)*B from mul_nonneg (Nat.cast_nonneg _) hv0) hr'; unfold P at he; linarith only [he]
   exact (c_mono V sold (hm _) (hm (v N')) (fun i hi=>hp0.trans_lt hi)).trans (h₀ N')
end YM.MSbar.Heath
