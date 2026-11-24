import YM.FormalOPE.RG10.Horizon.Confine
import YM.FormalOPE.RG10.Restriction
/-! # Coherence through order/rewrite approximants separately at r, using born valuation
Operators only in the given stencil positions. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Through
open Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD Panel Panel.Consumer InversionTop
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle Arrangements Apertures Transit Route Capture Weave Film
open scoped Topology BigOperators ContDiff Classical
open Clearing PowerSeries Clearing.Ledger Rates
variable {G:Gauge}{F:Frames G}{R:Rails F}{P:Plan F}{Y:Drivers}{Z:Patience P Y}{r m d h n:ℕ}
variable {A B C D: fps} {X:Type*} 
lemma neg (h:Through r A B): Through r (-A) (-B):= fun i hi=>by simp [h i hi]
lemma sub (h:Through r A B) (k:Through r C D) : Through r (A-C) (B-D):= fun i hi=>by simp [h i hi,k i hi]
lemma fare (h:Through r A B): Clearing.coin r A=Clearing.coin r B:= by rw [cstate,cstate]; apply sum_congr rfl; intro i hi; rw [h i (by simpa using hi)]
lemma warp (h:Through r A B) (s:ℝ): Through r (R.flow.warp s A) (R.flow.warp s B) := fun i hi=>by
 rw [Flow.through,Flow.through, h i hi]; congr 1; exact sum_congr rfl (fun j hj => congr_arg (· * _) (h _ ((mem_range.mp hj|>.le).trans hi)))
variable {f g : X→fps}{S:Finset X}
lemma sums (h:∀ i∈S,Through r (f i) (g i)): Through r (∑ i∈S,f i) (∑ i∈S,g i):= fun i hi=>by simp_rw [map_sum]; exact sum_congr rfl (fun j hj=> h j hj i hi)
lemma prods (h:∀ i∈S,Through r (f i) (g i)): Through r (∏ i∈S,f i) (∏ i∈S,g i):= by induction S using Finset.induction_on with
 | empty=> simp only [prod_empty]; exact refl _
 | insert i t hi ih=> rw [prod_insert hi,prod_insert hi]; exact mul (h i (by simp)) (ih (fun j hj=> h j (mem_insert_of_mem hj)))
variable {u v:Seats F d}
lemma linearAt (hu:∀ i, Through r (u i) (v i)) (L:Seats F d→ₗ[fps] fps): Through r (L u) (L v):= by rw [seating u,seating v]; simp_rw [map_sum,map_smul]; exact sums fun i _ => (hu i).mul (refl (L (seat i)))
lemma travel (hu:∀ i, Through r (u i) (v i))(s:ℝ) (i): Through r (trail R s u i) (trail R s v i):= by unfold trail vecMul dotProduct; exact sums fun j _=> ((hu j).warp s).mul (refl _)
end YM.FormalOPE.RG10.Through
namespace YM.FormalOPE.RG10.Clearing
open Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD Panel Panel.Consumer InversionTop
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle Arrangements Apertures Transit Route Capture Weave Film
open scoped Topology BigOperators ContDiff Classical
open PowerSeries Ledger Rates
variable {G:Gauge}{F:Frames G}{R:Rails F}{P:Plan F}{Y:Drivers}{Z:Patience P Y}{r m d h n:ℕ}
local notation "ι" => Deck F d
local notation "Ω" => Fin m→Deck F d
local notation "W" => Seats F d
private lemma edits {X:Type*}(t:Fin m→X)(s:Fin n→X)(i:Fin m)(x:X)[DecidableEq (Fin m)][DecidableEq (Fin (m+n))] : Fin.append (update t i x) s = update (Fin.append t s) (Fin.castAdd n i) x:= by
 funext k; refine Fin.addCases ?_ ?_ k <;> intro j
 · by_cases h:j=i; subst j; simp
   simp [update_of_ne h, update_of_ne ((Fin.castAdd_injective m n).ne h)] -- class issues
 have he: Fin.natAdd m j ≠ Fin.castAdd n i:=fun h=>by obtain hh:=congr_arg Fin.val h; simp at hh; omega
 simp [update_of_ne he]

private def datum {X : Type*}[AddCommMonoid X][Module fps X] (t: MultilinearMap fps (fun _:Fin (m+n)=> X) fps)(s:Fin n→X) : MultilinearMap fps (fun _:Fin m=>X) fps where
 toFun v:= t (Fin.append v s)
 map_update_add' u i x y := by simp_rw [edits,MultilinearMap.map_update_add] -- implicit Decidable Eq?
 map_update_smul' u i x y := by simp_rw [edits,MultilinearMap.map_update_smul]

variable (R Z)
local notation "rGr" => MultilinearMap fps (fun _:Fin m=>W)
variable (x:Fin m→Seats F d) (V : Panel.Consumer.Vantage F) (y : Fin n→ Seats F h)
    (M:Apertures.Halo)(E:Fore m)(t:ℝ)

def margin (T:Test (m+n)) : rGr fps := (datum (program (fun u=>R.adjust Z (max d h) ⟨⟨m+n,T⟩,u⟩)) (Panel.promote (le_max_right d h) ∘ y)).compLinearMap (fun _=>Panel.promoting (le_max_left d h))

lemma margins (T:Test (m+n)) : margin R Z y T x=see R Z y T x:= by
 unfold margin; rw [MultilinearMap.compLinearMap_apply]; exact program_eq ..
lemma propagation (f : rGr fps) : f x = valuation (fun i:Fin m→Deck F d=> f (seat ∘ i)) x:= by
 conv_lhs=> rw [show x=(fun i=>∑ j,(x i j) • seat j) from funext (fun i=>seating (x i)),MultilinearMap.map_sum]
 simp_rw [MultilinearMap.map_smul_univ]; unfold valuation; exact sum_congr rfl (fun i _=> mul_comm ..)
lemma forecasts_linear : burst R Z V t E x= valuation (fun i:Fin m→ Deck F d=>burst R Z V t E (seat ∘ i)) x:= by
 simp_rw [burst]; split<;> rename_i h
 · rw [← margins]; simp_rw [← margins]; exact propagation ..
 simp [valuation]

lemma forwards (i:Deck F h) : winter R Z M x E h t i= valuation (fun u:Fin m→Deck F d=>winter R Z M (seat ∘ u) E h t i) x := by
 unfold winter; simp_rw [Matrix.vecMul,dotProduct,forecasts_linear R Z x]
 simp_rw [valuation, Finset.sum_mul]; rw [sum_comm]; apply sum_congr rfl; intro _ _; exact sum_congr rfl (fun _ _=> by ring)
end YM.FormalOPE.RG10.Clearing
