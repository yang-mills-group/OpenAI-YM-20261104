import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card

/-! Paths of distinct compulsory failures on any finite graph of bounded range.
The true joint probability of *each set* of sites is used. No independence
or volume, separation or geometry dependent constant is introduced. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked.RemoteRoster
open Finset Set MeasureTheory
open scoped Classical BigOperators
variable {α X:Type*}[DecidableEq α]

def pathBook (next:α→Finset α)(x:α):ℕ→Finset (List α)
  | 0=>{[]}
  | k+1=>(next x).biUnion fun y=>(pathBook next y k).image (List.cons y)

theorem path_book_size (next:α→Finset α)(M:ℕ)(degree:∀x,(next x).card≤M)(x:α)(k:ℕ):
    (pathBook next x k).card≤M^k:=by
  induction k generalizing x with
  | zero=>simp [pathBook]
  | succ k ih=>
    calc
      _≤∑y∈next x,((pathBook next y k).image (List.cons y)).card:=card_biUnion_le
      _≤∑_y∈next x,M^k:=sum_le_sum fun y _=>card_image_le.trans (ih y)
      _=(next x).card*M^k:=by simp
      _≤M^(k+1):=by rw [pow_succ'];exact Nat.mul_le_mul_right _ (degree x)

theorem path_book_length (next:α→Finset α)(x:α)(k:ℕ){P:List α}(h:P∈pathBook next x k):P.length=k:=by
  induction k generalizing x P with
  | zero=>simpa [pathBook] using congrArg List.length (mem_singleton.mp h)
  | succ k ih=>
    obtain ⟨y,_,value⟩:=mem_biUnion.mp h
    obtain ⟨L,ent,rfl⟩:=mem_image.mp value
    simp only [List.length_cons,ih (x:=y) ent]

theorem path_book_take (next:α→Finset α)(x:α)(k m:ℕ){P:List α}(h:P∈pathBook next x k)(len:m≤k):
    P.take m∈pathBook next x m:=by
  induction m generalizing x P k with
  | zero=>simp [pathBook]
  | succ m ih=>
    obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega:k≠0)
    obtain ⟨y,hy,value⟩:=mem_biUnion.mp h
    obtain ⟨L,ent,rfl⟩:=mem_image.mp value
    exact mem_biUnion.mpr ⟨y,hy,mem_image.mpr ⟨L.take m,ih y k ent (by omega),rfl⟩⟩

def threaded (next:α→Finset α)(x:α)(k:ℕ)(E:Finset α→Set X):Set X:=
  ⋃P∈(pathBook next x k).filter List.Nodup,E P.toFinset

/-- An ordered walk can be stopped at the requested distance before counting.
The ratio of successive prices is the size of one actual jump wallet times
the true single-site rarity. All other failures remain unrestricted. -/
theorem path_probability [MeasurableSpace X](μ:Measure X)(next:α→Finset α)(M:ℕ)
    (degree:∀x,(next x).card≤M)(E:Finset α→Set X){ρ:ℝ}(rp:0≤ρ)
    (rare:∀D,μ.real (E D)≤ρ^D.card)(x:α)(k:ℕ):
    μ.real (threaded next x k E)≤((M:ℝ)*ρ)^k:=by
  let B:=(pathBook next x k).filter List.Nodup
  calc
    _≤∑P∈B,μ.real (E P.toFinset):=measureReal_biUnion_finset_le _ _
    _≤∑_P∈B,ρ^k:=by
      apply sum_le_sum;intro P hp
      obtain ⟨listed,simple⟩:=mem_filter.mp hp
      simpa only [List.toFinset_card_of_nodup simple,path_book_length next x k listed] using rare P.toFinset
    _=(B.card:ℝ)*ρ^k:=by simp only [sum_const,nsmul_eq_mul]
    _≤(M:ℝ)^k*ρ^k:=by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg rp _)
      exact_mod_cast ((card_filter_le _ _).trans (path_book_size next M degree x k))
    _=((M:ℝ)*ρ)^k:=(mul_pow ..).symm

theorem threaded_measurable [MeasurableSpace X](next:α→Finset α)(x:α)(k:ℕ)(E:Finset α→Set X)
    (em:∀D,MeasurableSet (E D)):MeasurableSet (threaded next x k E):=by
  apply Finset.measurableSet_biUnion;intro P _;exact em P.toFinset

end YM.Integration.FVA1Physical.Marked.RemoteRoster
