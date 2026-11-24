import YM.FVA2.Scale.Pace
/-!
# Genuine polynomial dependence on MS parameter (log ν as in `YM/MS`)

Proven here not by dilating DR flows but by reading on THE SAME regulator across all
parameter values. Peculiarity of this route: uses the *posted* arrays at finite regulator,
which have uncontrolled D entries yet are always within fixed-degree polynomial. Uses no
limit assumption on those entries and no degree packing covariant approximations from
auxiliary IR computations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Scale
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open Dframe
open scoped Topology ContDiff BigOperators Classical
variable {I W:Type*}
namespace Pace
def formal (f:I→ℝ→ Cn) := ∀ n:ℕ, Pace (fun i t=> coeff n ( f i t ))
namespace formal
variable {f g: I→ℝ→ Cn}
lemma fixed (f:I→ Cn): formal (fun i _=> f i):= fun _=> narrow _
lemma add (h:formal f)(he:formal g): formal (fun i t=> f i t+g i t):= by
    intro i; simp_rw [map_add]; exact (h i).add (he i)
lemma mul (h:formal f)(he:formal g): formal (fun i t=> f i t*g i t):= by
    intro i; simp_rw [coeff_mul]; exact Pace.sum _ fun x _=> Pace.mul (h x.1) (he x.2)
lemma neg (h:formal f): formal (fun i t=> -f i t):= by
    intro i; simp_rw [map_neg]; exact Pace.neg (h i)
lemma pow (h:formal f) (k:ℕ): formal (fun i t=>f i t^k):= by induction k with| zero=>simp only [pow_zero]; exact fixed _| succ i ih=>simp only [pow_succ]; exact ih.mul h
lemma prod {H: W→ I→ℝ→ Cn}(s: Finset W)(h:∀ i∈s,formal (H i)): formal (fun i t=> ∏ j∈s, H j i t):= by
    induction s using Finset.induction_on with
    | empty=> simp only [Finset.prod_empty]; exact fixed _
    | insert i s hi ih=> simp only [Finset.prod_insert hi]; exact mul (h i ( Finset.mem_insert_self .. )) (ih fun j hj=> h _ (Finset.mem_insert_of_mem hj))
lemma substitute (h:formal f)(he:formal g)(H:∀ i t, Rooted (g i t)): formal (fun i t=> (f i t).subst (g i t)):= by intro i; simp_rw [← Constants.actual_subst _ _ ( H .. ),coeff_mk,rules,smul_eq_mul]; exact Pace.sum _ fun j _=> Pace.mul ( he.pow j i ) (h j)
lemma apply {h:I→ℝ→MS.Book.Convolve.T ℂ}(he:∀ n,Pace (fun i t=> h i t n))(H:formal g): formal (fun i t=> PowerSeries.mk (Program.substitute (g i t) (h i t))):= by intro i; simp_rw [coeff_mk,rules,smul_eq_mul]; exact Pace.sum _ fun j _=> Pace.mul (H.pow j i) (he j)
lemma smul (h:formal f)(z:ℂ): formal (fun i t=> z • f i t):= by intro i; simp_rw [map_smul,smul_eq_mul]; exact Pace.mul (narrow _) (h i)
end formal
end Pace
namespace Known
variable {I:Type*}{G:Gauge}(Y:Initialize G)(S: Prescription (Press.portDeck G)){O:Booked (Press.portDeck G)} (T: MS_Data G O)
local notation "μ"=> ( PowerSeries.mk (R:=ℂ) )
lemma shifts (f:I→Mesh) : Pace.formal (fun i t=> Dframe.reset t S (f i)):= by
    intro i; unfold reset; simp_rw [ MS.Book.Program.shift, coeff_mk ]; split_ifs <;> first| exact Pace.narrow _| apply Pace.prime _ _
variable {n d:ℕ}
lemma returns (f:I→Mesh) (a:Toon G d)(b:Toon G a.size) : Pace.formal (fun i t=> Dframe.allows t S (f i) a b):= by
    intro i; simp_rw [allows, coeff_mk, stake, Complex.ofReal_mul]; exact Pace.mul ( Pace.narrow _ ) ( Pace.prime _ _ ) -- ink
lemma serves (p:Tags G d n)(f:I→Sample n): Pace.formal (fun i t=> Reg.Point.story ( postedPoint t Y S d (f i) ) p):= by
    intro k; have ht (y:Fin n→ Toon G d): Pace (fun i:I=> fun t:ℝ=> postedPoint t Y S d (f i) k (fill y)) := by
        simp_rw [ ← show ∀ i t, coeff k ( Reg.Point.story ( postedPoint t Y S d (f i) ) (fill y) )= _ from ( show ∀ i t, coeff k (Reg.Point.story ( postedPoint t Y S d (f i) ) (fill y) )= postedPoint t Y S d (f i) k (fill y) from fun i t=> coeff_mk .. ) ]; unfold Reg.Point.story; simp_rw [ meeting, ← store_s, map_sum ]; refine Pace.sum _ (fun j _=>?_); -- rewrite `orderT` price shift w constant
        simp_rw [ Dframe.orderT, Dframe.translate ]; exact Pace.formal.mul ( Pace.formal.prod (H:=fun (a:Fin n) i t=> Dframe.allows t S (f i).F (y a) (j a)) _ (fun a _=> returns S ( fun i=> (f i).F ) (y a) (j a)) ) ( Pace.formal.apply ( fun i=> Pace.narrow _ ) ( shifts S (fun i=> (f i).F) ) ) k -- may mismatch parentheses
    simp_rw [Reg.Point.story,coeff_mk, stencil_he ( postedPoint _ _ _ _ _ _ ) p ]; exact Pace.sum _ fun i _=> ( Pace.narrow _|>.mul ( ht i ))
variable (h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)(hr:Favors.Horder S)(hu:Ace.UnitP S)
include h hs
theorem rhythm (x:Points n)(he:x∈conf n)(v:Tags G d n)(k:ℕ) : Rhythm (fun i=> meteor i T d x k v):= by
    apply Pace.limit ( F:= Gate x ) ( serves Y S v id k ); intro i; simp_rw [Reg.Point.story,coeff_mk]; exact tB i Y S T h hs k v x he
include hr hu
theorem method {P:Normalize.Store G}(K:Rose.Pick P)(k:ℕ): Rhythm (fun i => coeff k (Reg.Choice.choice i K T)):= by
    let p:= fun m i=> Reg.Choice.prospects i Y K S m
    apply Pace.limit ( F:= Front ) ((show Pace.formal p from Pace.formal.substitute ( Pace.formal.fixed _ ) ( shifts S id ) (fun _ t=> MS.Book.Program.share .. )
     ) k)
    intro i; exact Reg.Choice.forecast i Y K S T h hs hr hu k
end Known
end YM.FVA2.Scale
