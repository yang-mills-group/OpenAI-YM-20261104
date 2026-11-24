import YM.FVA2.Scale.Native
/-!
# Change of measuring length on the *actual* P=even regulator filtration.

Periods need not match under interpolation from some coarsening chain, because
here the theorem already works with `Front`. Keep F.p identical, including anchor
root of chart. This preserves the finite-reg relation after explicit engineering powers
for all fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Scale.Extent
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open Dframe
open scoped Topology ContDiff BigOperators Classical
variable (t:ℝ) {n d k:ℕ}
local notation "a"=> ( Real.exp ( - t ) )
def march (m: Mesh): Mesh:= ⟨ m.p,a*m.spacing,mul_pos (Real.exp_pos _) m.positive⟩
lemma bill (m:Mesh): ( march t m ).size= a * m.size:= by unfold Mesh.size march; dsimp only; ring
lemma ridge : Tendsto (march t) Front Front:= by
    apply goesFront; constructor; · have h:= frontier.endpt.const_mul a; rw [mul_zero] at h; exact h
    intro i; let r:= a^i; have he(x:Mesh): (XSpace.Expense.a (march t) x)^i * XSpace.Expense.sides (march t) x= r*(x.spacing^i * (↑x.p.side.val:ℝ)):= (by change ( a*x.spacing )^i * _= r * (x.spacing^i * _); rw [mul_pow,mul_assoc]; rfl);
    exact (( frontier.pay i ).const_mul_atTop ( show 0<r from pow_pos (Real.exp_pos _) _ ) ).congr (fun x=> (he x).symm )
-- scaled coordinates always smaller for t>0. uses real positive all t.
variable (p: Points n)
local notation "r"=> ( a • p )
def reaches (u:Sample n): Sample n:= ⟨march t u.F,u.layout,a • u.center⟩
lemma familiar_r (u:Sample n): familiar (reaches t u)= a • ( familiar u ):= by
    unfold familiar Mesh.rel reaches; ext1 i; change (a*u.F.spacing) • WithLp.toLp 2 _ - WithLp.toLp _ _= a • (u.F.coord (u.layout i) - _); rw [mul_smul,smul_sub]; rfl
lemma travels (u:Sample n)(h: welcome u): welcome (reaches t u):= by
    rcases h with ⟨ hp,hq ⟩; constructor <;> intro i <;> specialize hp i <;> specialize hq i; · change ( march t u.F ).size/8 ≤ a*u.center i; rw [bill, mul_div_assoc]; exact mul_le_mul_of_nonneg_left hp (Real.exp_pos _|>.le)
    change a*u.center i ≤ ( march t u.F ).size /4; rw [bill,mul_div_assoc]; exact mul_le_mul_of_nonneg_left hq (Real.exp_pos _|>.le)
lemma knocks : Tendsto ( reaches t ) ( Gate p ) (Gate (a • p)):= by
    rw [Gate,Gate,tendsto_inf,tendsto_inf]
    refine ⟨⟨ tendsto_comap_iff.mpr ?_, tendsto_comap_iff.mpr ?_⟩, tendsto_principal.mpr ?_⟩; · exact ( ridge t ).comp ( liftG p )
    · exact ((senseG p).const_smul a).congr (fun i=> ( familiar_r t i ).symm)
    exact (welcomeG p).mono fun v hv=> travels t v hv
lemma placed (h:p∈conf n): ( a • p )∈ conf n:= by intro i j h'; apply h; exact smul_right_injective E4 ( Real.exp_pos (-t) |>.ne' ) h'
-- cutoff profile θ and shifted-coupling argument.
lemma post (ν:ℝ): ∀ᶠ i in Front, ν- Schedule.theta ( march t i ) = (ν-t)-Schedule.theta i:= by
    filter_upwards [( ridge t ).eventually frontier.smaller, frontier.smaller] with i hi h
    rw [ Schedule.theta_value (m:=march t i) hi, Schedule.theta_value (m:=i) h ]; unfold march; dsimp only; rw [Real.log_mul (Real.exp_pos _|>.ne') i.positive.ne', Real.log_exp ]; ring
variable {G:Gauge} (ν:ℝ) (Y:Initialize G)(S: Prescription (Press.portDeck G)){O:Booked (Press.portDeck G)} (T: MS_Data G O)
abbrev token (t:ℝ)(d:ℕ):ℂ:= ( (Real.exp (-t):ℝ):ℂ )^d
theorem priced (u:Fin n→Toon G d)(v:Sample n) (h:ν-Schedule.theta (march t v.F)=(ν-t)-Schedule.theta v.F):
    postedPoint ν Y S d ( reaches t v ) k (fun i=>token t (u i).size • fill u i)= postedPoint (ν-t) Y S d v k (fill u):= by
    rw [ MultilinearMap.map_smul_univ ( postedPoint ν Y S d ( reaches t v ) k ) (fun i=> token t (u i).size) (fill u), smul_eq_mul, reads _ _ _ _ _,reads _ _ _ _ _ ]; unfold Schedule.entries reaches; dsimp only [ march ]; -- θ rewriting check
    change ( ∏ i, token t ( u i ).size ) * ( (( (a*v.F.spacing:ℝ):ℂ)^_ )⁻¹ * Top.value Y (flash ∘ u ) S 0 v.layout v.F.p.side (ν-Schedule.theta (march t v.F)) Finset.univ k )= _; rw [h, ← mul_assoc (∏ i, token t (u i).size), Complex.ofReal_mul, mul_pow, mul_inv, flash_time ]; unfold token; -- flash_time implicit no mesh
    rw [ Finset.prod_pow_eq_pow_sum ]; simp only [ ← mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _|>.ne'))),one_mul]
variable (h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)
include h hs
lemma declares (u:Fin n→ Toon G d)(H:p∈conf n) : meteor ν T d ( a • p ) k ( fun i=> token t (u i).size • fill u i)= meteor (ν-t) T d p k (fill u):= by
    apply tendsto_nhds_unique ( ((tB ν Y S T h hs k _ _ ( placed t p H ) ) ).comp ( knocks t p ) ) _; refine ( tB (ν-t) Y S T h hs k _ p H ).congr' ?_ ; filter_upwards [( liftG p ).eventually ( post t ν )] with i hi; exact (priced t ν Y S u i hi).symm
end YM.FVA2.Scale.Extent
