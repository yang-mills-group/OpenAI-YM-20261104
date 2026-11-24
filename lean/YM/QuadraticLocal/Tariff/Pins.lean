import YM.RG3.Annuncia.Revenue
import YM.QuadraticLocal.Deletion.Absence
/-!
# Mark occurrences with allocated names (`Replica`) — partial evaluation re-expression

In the same supported E.log/K representation. Occupations labelled with W, mapped
 to V (may be many-to-one); preserve every root and budget on the move. Fin.Count.Work
 C*(ν_B_Frame.We.Body) etc when marked.W then closure of map.Key.Request.Region.Height metadata.`
 This handles temporary τ projection for *any* subset of modes, with its own
 occupation norms (use for estimates with the product of old eps factors or input norms, not
 only after valuation and collapse). The actual representation is then chosen with *all*
 modes simultaneously for all these λ settings.
 Not asserting `Slice` treats exponential/passive disconnected Φ by the same supported-Ledger price.
 Continue by product.S.Doc.Year. Art precision uses CleanTag.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Tariff
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 RG3.Annuncia RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Fusion Attached Push.Local
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {p : BudgetPoint}
variable {V W : Type} [DecidableEq V] [Fintype V][DecidableEq W][Fintype W]
variable (u:W→ V) (R: Census V) (o : V→Site n)
local notation "S"=> (Annuncia.Replica u R)
local notation "ϕ"=> ( Annuncia.Replica.bill u R )
variable (γ:(Replica u R).Mode→ℂ)
variable (w:V→ℝ)(hw:∀ i,0<w i)
variable {T J η : Type*} {a b c δ ε :ℝ}{B B' :ℕ}
local notation "ν"=> ( w ∘ u )
-- non-product per-mode prices for selecting exact subquotations from a λ history citation.
-- .. all still public.C.Term.Work.Sensor.E.State_H.Clock lift all witnesses. Returns only linear stencil participation (need retain exact merge through Traveler separately).
def pay : Poly S→ₗ[ℂ] Poly R where
    toFun x:= Poly.inject fun i=> ∑ j: (S).Mode, if ϕ j=i then γ j * x.part j else 0
    map_add' x y:= by
        ext i; rw [Poly.part_plus]; change (∑ j:(S).Mode,if ϕ j=i then _ else _)= (∑ j:(S).Mode,if ϕ j=i then _ else _)+(∑ j:(S).Mode,if ϕ j=i then _ else _); rw [← sum_add_distrib]; refine sum_congr rfl fun j _=>?_ ; split; rw [Poly.part_plus, mul_add]; exact (zero_add _).symm
    map_smul' r x:= by
        ext i; rw [Poly.part_smul]; change (∑ j:(S).Mode, if ϕ j=i then _ else _) = r* ∑ j:(S).Mode,(if ϕ j=i then _ else _); rw [mul_sum]; apply sum_congr rfl; intro j _; split; simp_rw [Poly.part_smul]; exact mul_left_comm ..; exact (mul_zero _).symm
lemma quota (x:Poly S)(i:R.Mode): (pay u R γ x).part i= ∑ j: (S).Mode, if ϕ j=i then γ j * x.part j else 0:=rfl
-- test-sup uniform profile on EACH activated j. BEFORE linear projections & polyn.Resource.
lemma toll (s:(S).Mode):Poly.toll ν s=Poly.toll w (ϕ s):= by
   unfold Poly.toll Replica.bill; rw [ prod_image (fun _ ha _ hb ht=> (Replica.admit u R s|>.separate) ha hb ht )]; rfl
-- any Arc within size bound.HasSum uniform Vol.Entry
local notation "vΛ" i:max=> (ϕ i)
variable (C:(Replica u R).Mode→ℝ)(hC:∀ v, ‖γ v‖≤ C v)
noncomputable def amount (f: ( Replica u R ).Mode →ℝ) (s:R.Mode): ℝ:= ∑ i:(S).Mode, if ϕ i=s then C i*f i else 0
include hC
lemma salary (f:(S).Mode→ℝ)(x:Poly S)(hf:∀i,‖x.part i‖ ≤ f i)(s:R.Mode): ‖(pay u R γ x).part s‖ ≤ amount u R C f s := by
    rw [quota]; apply ( norm_sum_le _ _ ).trans; apply sum_le_sum; intro i _; by_cases h:ϕ i=s; · simp only [h,↓reduceIte,norm_mul]; exact mul_le_mul (hC i) (hf i) (norm_nonneg _) ((norm_nonneg _).trans (hC i))
    rw [if_neg h,if_neg h,norm_zero] -- RHS unfolded by apply sum?
omit hC
lemma costP (f:(Replica u R).Mode→ℝ): ( ∑ i:R.Mode, Poly.toll w i * amount u R C f i )= ∑ i:( S ).Mode, Poly.toll ν i*(C i*f i):= by
    unfold amount; simp_rw [mul_sum]; rw [ sum_comm ]; refine sum_congr rfl fun i _=>?_ ; rw [sum_eq_single_of_mem (ϕ i) (mem_univ _) (fun j hj hv=>?_), if_pos rfl]; rw [toll]; rw [if_neg (Ne.symm hv),mul_zero] -- _goals order
noncomputable def charge (x: Poly (Replica u R)): Poly R:= Poly.inject fun j=> (amount u R C (fun i=> ‖x.part i‖) j:ℂ)
include hC
lemma cap (x y:Poly S)(h:Width.Covered x y): Width.Covered (pay u R γ x) (charge u R C y):= by
    intro i; refine ⟨ salary u R γ C hC _ _ (fun i=> (h i).1.trans_eq (h.norm i).symm) _ , rfl ⟩
include hw
lemma area (x:Poly S)(he:∀ i,C i≤ ε): Poly.price w ( charge u R C x ) ≤ ε* Poly.price ν x:=by
    have hx(s:R.Mode) : 0≤ amount u R C (fun i=> ‖x.part i‖) s:= sum_nonneg (fun i _=> by split; exact mul_nonneg ( (norm_nonneg _).trans (hC i) ) (norm_nonneg _); exact le_rfl )
    have hz(i:R.Mode): ‖(charge u R C x).part i‖= amount u R C (fun i=> ‖x.part i‖) i:= by change ‖((amount u R C (fun i=> ‖x.part i‖) i):ℂ)‖= _; simp only [Complex.norm_real, Real.norm_of_nonneg (hx _)]
    unfold Poly.price; simp_rw [hz]; rw [costP, mul_sum]; refine sum_le_sum fun i _=>?_ ; let p:= Poly.toll ν i; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (he i) (norm_nonneg _)) ( show 0≤p from ( Poly.worth (fun i=> hw (u i)) _ ).le )).trans_eq (show p*(ε* _) =_ from by ring)
end YM.QuadraticLocal.Tariff
