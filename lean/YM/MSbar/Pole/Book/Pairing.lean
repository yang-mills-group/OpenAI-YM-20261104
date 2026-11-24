import YM.MSbar.Pole.Book.Panel
/-! # Compute canonical local odd and even vertices from traditional Lorentz contractions -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Book
open Function Set Filter MeasureTheory Momentum Ambient Age Mellin place Symbol Sew Thread Feynman District
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {I : Type} [Fintype I]

abbrev Links (I) := List (I × I)
def links (b : Links I) (n : ℕ) (x:External I n):ℂ:= (b.map fun v=> ((inner ℝ (x v.1) (x v.2):ℝ):ℂ)).prod
def tour (b : Links I): List I:= b.flatMap fun x=>[x.1,x.2]
def amount (M:Finset I) (b : Links I) := ((tour b).filter (· ∈ M)).length

@[simp] lemma empty (n) (x :External I n):links [] n x=1:=rfl
@[simp] lemma another (p q:I)(L:Links I)(n)(x:External I n): links ((p,q)::L) n x= (inner ℝ (x p) (x q):ℝ)*links L n x:=rfl
lemma canon (b:Links I): Canonical (links b) := by
  induction b with
  | nil=> exact ⟨⟨fun _ _ _=>rfl,fun _ _=>rfl⟩,fun _=>Packet.const 1⟩
  | cons a b ih=>
    obtain ⟨p,q⟩:=a; have hj {n:ℕ} (i:I):Packet univ (ticket (@id (External I n))) 1 (fun x:External I n=> x i):= Packet.built (ContinuousLinearMap.hasTemperateGrowth (ContinuousLinearMap.proj i:External I n →L[ℝ] place n)) Bills.self
    constructor
    · constructor
      · intro n J x; rw [another,ih.1.moves,another]; simp
      intro n x; rw [another,ih.1.agrees,another]; simp
    intro n; exact Packet.mul ((Packet.bilinear (hj p) (hj q) (innerSL ℝ)).apply (X:=Complex.ofRealCLM)) (ih.2 n)

lemma grades (b:Links I)(M:Finset I) : Local M (-(amount M b:ℕ)) (links b):= by
  constructor
  · exact canon b
  · simp
  intro n x t ht
  induction b with
  | nil=> simp [amount,tour]
  | cons a b ih=>
    obtain ⟨p,q⟩:=a
    simp only [another,neg_neg,zpow_natCast] at *
    by_cases hp:p∈M<;>by_cases hq:q∈M<;> rw [ih] <;> unfold amount tour <;> simp [move,hp,hq,pow_add,inner_smul_left,inner_smul_right] <;> ring

lemma detects (b:Links I): Listen (tour b).toFinset (links b):= by
  induction b with
  | nil=>exact fun _ _ _ _=>rfl
  | cons a b ih=>
    obtain ⟨p,q⟩:=a; intro n x y hh
    rw [another,another, ih n x y fun i hi=>hh i (by simp [tour] at hi ⊢; exact Or.inr (Or.inr hi)), hh p (by simp [tour]), hh q (by simp [tour])]

lemma bent (b:Links I) (v:I) (h:(tour b).count v=1) : Tone (links b) v:= by
  induction b with
  | nil=> simp [tour] at h
  | cons a b ih=>
    intro n x; obtain ⟨p,q⟩:=a
    by_cases hp : p=v
    · subst p; by_cases hq:q=v
      · subst q; simp only [tour,List.flatMap_cons,List.count_append,List.count_cons_self,List.count_nil] at h; omega
      have hv:v ∉ (tour b).toFinset:= by simp only [tour,List.flatMap_cons,List.count_append,List.count_cons_self,List.count_cons_of_ne hq,List.count_nil] at h; simp [List.count_eq_zero.mp (show (tour b).count v=0 by unfold tour; omega)]
      have hx (a:place n): links b n (update x v a) = links b n x:= detects b n _ _ fun i hi=>update_of_ne (ne_of_mem_of_not_mem hi hv) _ _
      simp_rw [another,hx,update_self,update_of_ne hq]
      exact ⟨fun u v=>by rw [inner_add_left]; push_cast; ring, fun r t=>by rw [real_inner_smul_left]; push_cast; rw [Complex.real_smul,mul_assoc]⟩
    by_cases hq:q=v
    · subst q
      have hv:v ∉ (tour b).toFinset:= by simp only [tour,List.flatMap_cons,List.count_append,List.count_cons_of_ne hp,List.count_cons_self,List.count_nil] at h; simp [List.count_eq_zero.mp (show (tour b).count v=0 by unfold tour; omega)]
      have hx (a:place n): links b n (update x v a) = links b n x:= detects b n _ _ fun i hi=>update_of_ne (ne_of_mem_of_not_mem hi hv) _ _
      simp_rw [another,hx,update_self,update_of_ne hp]
      exact ⟨fun u v=>by rw [inner_add_right]; push_cast; ring, fun r t=>by rw [real_inner_smul_right]; push_cast; rw [Complex.real_smul,mul_assoc]⟩
    have hp': (tour b).count v=1:= by simpa [tour,List.count_cons,hp,hq] using h
    simp_rw [another,update_of_ne hp,update_of_ne hq]; exact (ih hp' n x).scale _
end YM.MSbar.Pole.Book
