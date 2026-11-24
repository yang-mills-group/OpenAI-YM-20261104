import YM.AllOrder.Till.Compress
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Till
open Lattice Laurent RG Gauge Filter Tree Metric Finset Bloch
open Push.Uniform Precision Bid Wilson Push Exterior Pressure Function Matrix
open Extra.Iteration Push.AbsoluteSums Plateau
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {k w:ℕ} {n : Side}
local notation "T" => RG.Atom G k
def Plan (k w:ℕ):= {v:Fin k→Slot// ∑ i,(v i).length ≤ w}
local instance : Finite Lattice.Step:= Finite.of_surjective (fun p:Axis×Bool=> Lattice.Step.mk p.1 p.2) fun i=>⟨⟨i.dir,i.neg⟩,rfl⟩
instance : Fintype (Plan k w):= by
 refine (Set.Finite.fintype (s:={v:Fin k→Slot| ∑ i,(v i).length ≤ w}) ?_)
 let v:Set Slot:= {s|s.length ≤ w}; have hv:v.Finite:= by
     let f:Walk×PlaqAxes→Slot:= fun p=>⟨p.1,p.2⟩; refine (((List.finite_length_le Lattice.Step w).prod (Set.finite_univ (α:=PlaqAxes))).image f).subset fun s hs=> ?_; refine ⟨(s.walk,s.plaq),⟨?_, Set.mem_univ _⟩,rfl⟩; change s.length ≤ w at hs; change s.walk.length≤_; unfold Slot.length at hs; omega
 refine (Set.Finite.pi (ι:=Fin k) (fun _ => hv)).subset fun f hf=>?_ ; intro i _; exact (Finset.single_le_sum (f:= fun i=> (f i).length) (fun _ _=>Nat.zero_le _) (mem_univ i)).trans hf
-- grouping support compresses full costs.
variable {p:ℕ→Atom G k} (hW: ∀ i,(p i).length ≤ w)
local notation "I" => Plan k w
def planned (i:I)(s:ℕ): Prop:= (p s).leg = (show {v : Fin k → Slot // ∑ i, (v i).length≤w} from i).1
namespace Plan
abbrev feet (i:Plan k w): Fin k→Slot:= (show Subtype _ from i).1 -- parser likely
end Plan
def pillar(p:ℕ→Atom G k)(i:I): T where
 leg := i.feet
 coeff a:= ∑' j:ℕ, if planned (p:=p) i j then (p j).coeff a else 0
lemma life (p:ℕ→T)(i:I): (pillar p i).length ≤ w:= Subtype.property i
variable {t C δ:ℝ} (p) (h:Charged p t C)(ht:0<t)
def insideS {ι E:Type*}[Zero E](f:ι→E)(n:ι)(i:Plan k w)(j:ℕ): E:= if planned (p:=p) i j then f n else 0
abbrev cvar:=Fin k → G.ColorIndex
variable {p}
lemma subS {E:Type*}[NormedAddCommGroup E][CompleteSpace E]{f:ℕ→E}(i:Plan k w)(h:Summable f): Summable (fun j=> if planned (p:=p) i j then f j else 0):= by
 exact Summable.indicator h {j:ℕ| planned (p:=p) i j} -- may Complete
variable (p)
include hW
lemma joinS {E:Type*}[NormedAddCommGroup E][CompleteSpace E](f:ℕ→E)(h:Summable f): (∑ i:I,∑' j:ℕ, if planned (p:=p) i j then f j else 0)=∑' j,f j:= by
 rw [← Summable.tsum_finsetSum (fun (i:Plan k w) (hi:i∈Finset.univ)=> subS (p:=p) i h)]; apply tsum_congr; intro j; let i₀:I:= ⟨(p j).leg,hW j⟩; rw [sum_eq_single i₀,if_pos (show planned i₀ j from rfl)] -- fill side
 · intro i hi hh; apply if_neg; intro hx; exact hh (Subtype.ext (Eq.symm hx))
 simp
omit hW
include h ht
lemma c_bill (a:Fin k→G.ColorIndex)(i:Plan k w): Summable (fun j:ℕ=> if planned (p:=p) i j then (p j).coeff a else 0):= subS i <| (Summable.of_norm_bounded (h.absolute ht.le) fun i=> Extra.Iteration.coeff_le (p i) a)
lemma charter (i:Plan k w)(x:Fin k→G.Color): (pillar p i).poly x=∑' j:ℕ, if planned (p:=p) i j then (p j).poly x else 0 := by
 unfold Atom.poly; simp only [pillar]; simp_rw [← (c_bill p h ht _ i).tsum_mul_right]; rw [← Summable.tsum_finsetSum (fun a _=> (c_bill p h ht a i).mul_right _)]; exact tsum_congr fun j=>by split<;> simp [*]
lemma remit (i:Plan k w)(x:Site n)(U:Config G n): (pillar p i).unmasked U x=∑' j:ℕ, if planned (p:=p) i j then (p j).unmasked U x else 0 := by
 rw [Atom.unmasked, charter p h ht i]; apply tsum_congr; intro j; split; next hh=> unfold Atom.unmasked; rw [show (p j).leg=i.feet from hh]; rfl
 next ht=> rfl
lemma turns (i:Plan k w)(hs:SymmetricAtoms p): (pillar p i).Invariant:= by intro u x; rw [charter p h ht,charter p h ht]; exact tsum_congr (fun j=>by split; exact hs j ..; rfl)
include hW
lemma total (x:Site n)(U:Config G n): (∑' j:ℕ,(p j).unmasked U x)= ∑ i:I, (pillar p i).unmasked U x:= by simp_rw [remit p h ht]; exact (joinS p hW _ (Plateau.summation p ht h ..)).symm -- arg p order?
private lemma amount1 (i:Plan k w) : (pillar p i).magnitude ≤ ∑' j:ℕ,if planned (p:=p) i j then (p j).magnitude else 0 := by
 let f (a:Fin k→G.ColorIndex) j:= if planned (p:=p) i j then (p j).coeff a else 0; have hf a:= c_bill p h ht a i
 calc
  _ ≤ ∑ a:Fin k→G.ColorIndex, ∑' j:ℕ,|f a j|:= by unfold Atom.magnitude; refine sum_le_sum fun a _=>?_ ; exact norm_tsum_le_tsum_norm (f:=f a) (hf a).abs -- maybe lemma
  _ = _:= by rw [← Summable.tsum_finsetSum (fun a _=> show Summable (fun j=>|f a j|) from (hf a).abs)]; refine tsum_congr fun j=>?_ ; split <;> simp [*,f,Atom.magnitude]
lemma priceF : Charged (pillar p (w:=w)) t C:= by
 refine budget_finite (fun i=>paid_nonneg ..) <| le_trans (sum_le_sum (g:=fun i=> ∑' j, if planned (p:=p) i j then (p j).budget t else 0) fun i _=>?_) ((joinS p hW _ h.2.1).le.trans h.2.2)
 let d:=(pillar p i).length; let g:=Real.exp (t*d); refine (mul_le_mul_of_nonneg_right (amount1 p hW h ht i) (Real.exp_pos _).le).trans_eq ?_; let f j:= if planned (p:=p) i j then (p j).magnitude else 0; change (∑' j,f j)*g=_; rw [← (subS (p:=p) i (h.absolute ht.le)).tsum_mul_right]; refine tsum_congr fun j=>?_ ; split; next hh=> unfold Atom.budget; rw [show (p j).length=d from congr_arg (fun s:Fin k→Slot=>∑ i:Fin k, (s i|>.length)) hh] -- type
 next hh=> simp
-- preserves charge
end YM.AllOrder.Till
