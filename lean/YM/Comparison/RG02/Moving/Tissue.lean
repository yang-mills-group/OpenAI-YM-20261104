import YM.Comparison.RG02.Moving.Path
/-!
# The tissue of a real analytic-germ marker board
 Real germ through fixed E (here ℝ) orders. Ordinary Fréchet using ω germs.
 Not prices. Used when charging positive-grade cumulants before taking the exponentials
 of logs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Moving
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree YM.Next.Rank
open YM.Precision YM.Next.SectorChange Gaussian Affinity Cumulants
open PertExtension.Series PertExtension.Series.Tested Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal

namespace Shift
open Path
variable {f g : ℝ→ℂ} {k : ℕ}
local notation "ℱ" => (ω:WithTop ℕ∞)
lemma mconst (p:ℂ) (k:ℕ) : motion (fun _=>p) k=if k=0 then p else 0 := by
   cases k with
   | zero=> simp [motion]
   | succ i=> rw [motion, Assembly.jet,iteratedFDeriv_const_of_ne (by omega : i+1≠0),if_neg (by omega)]; simp
lemma mscale (p:ℂ) (hf : ContDiffAt ℝ ℱ f 0) : motion (fun x=>p*f x) k=p*motion f k :=
   (Assembly.jet_apply_left (ContinuousLinearMap.mul ℝ ℂ p) f k (hf.of_le le_top) 1).symm
lemma mgerm (h : f =ᶠ[𝓝 0] g) : motion f k=motion g k := by unfold motion Assembly.jet; rw [(h.iteratedFDeriv ℝ k).eq_of_nhds]
lemma madd (hf : ContDiffAt ℝ ℱ f 0) (hg : ContDiffAt ℝ ℱ g 0) : motion (fun x=> f x+g x) k=motion f k+motion g k := congrFun ((ordinary (f:=f+g) (hf.add hg|>.of_le le_top)).unique ((ordinary (hf.of_le le_top)).add (ordinary (hg.of_le le_top)))) _
lemma mprod (hf : ContDiffAt ℝ ℱ f 0) (hg : ContDiffAt ℝ ℱ g 0) : motion (fun x=> f x*g x) k =∑ i∈ antidiagonal k,motion f i.1 * motion g i.2:= by
   have he := (ordinary (f:=f*g) (hf.mul hg|>.of_le le_top)).unique ((ordinary (hf.of_le le_top)).prod (ordinary (hg.of_le le_top))); change motion (f*g) k=_
   rw [he]; simp only [Tested.conv,term,PowerSeries.coeff_mul, PowerSeries.coeff_mk]
lemma msum {ι:Type*} (L : Finset ι) (f : ι→ℝ→ℂ) (hf : ∀ i∈L,ContDiffAt ℝ ℱ (f i) 0) : motion (fun x=> ∑ i∈L,f i x) k= ∑ i∈L,motion (f i) k:= by
   classical
   induction L using Finset.induction with
   | empty => simp
   | insert i u hi ih=> simp_rw [sum_insert hi]; rw [madd (hf i (mem_insert_self ..)) (ContDiffAt.sum fun i hi=> hf i (mem_insert_of_mem hi)),ih (fun i hi=>hf i (mem_insert_of_mem hi))] -- eta
lemma mzero : motion f 0=f 0 := by simp [motion]
variable {V : Type} [DecidableEq V] {R : Census V} {u v : ℝ → Poly R}

def sight (u : ℝ → Poly R) (k : ℕ) : Poly R:= Poly.inject (fun i=> motion (fun x=> (u x).part i) k)
lemma sight_at (s:R.Mode) : (sight u k).part s=motion (fun x=> (u x).part s) k:=rfl
lemma sight_congr (h : u=ᶠ[𝓝 0] v) : sight u k=sight v k := by ext i; rw [sight_at,sight_at]; exact mgerm (h.mono fun _ he=> congrArg (fun z=> Marker.Poly.part z i) he)
lemma sight_0 (u : ℝ→Poly R) : sight u 0=u 0:= by ext i; rw [sight_at]; exact mzero
lemma sight_save (x:Poly R) (k:ℕ) : sight (fun _=>x) k=if k=0 then x else 0 := by ext s; rw [sight_at, mconst]; split <;> rfl
local notation "ℓ"=> 𝓝 (0:ℝ)
structure Seen (u : ℝ → Poly R) : Prop where
   smooth (i:R.Mode): ContDiffAt ℝ ℱ (fun x=> (u x).part i) 0
lemma Seen.even (u : Poly R) : Seen (fun _=>u):= ⟨fun _=>contDiffAt_const⟩
variable (hu : Seen u) (hv : Seen v)
include hu
lemma Seen.changeOf (h : u=ᶠ[ℓ] v) : Seen v:= ⟨fun i=> (hu.smooth i).congr_of_eventuallyEq (h.symm.mono fun _ hx=> congrArg (fun y=> Marker.Poly.part y i) hx)⟩
lemma Seen.scale (z : ℂ) : Seen (fun x=> z • u x) := by constructor; intro s; simp_rw [Poly.part_smul]; exact contDiffAt_const.mul (hu.smooth s)
lemma Seen.scaled (p:ℂ) : sight (p • u) k=p • sight u k := by ext i; rw [Poly.part_smul,sight_at,sight_at]; exact mscale p (hu.smooth i)
include hv
lemma Seen.gathers : Seen (u+v) := ⟨fun _=> (hu.smooth _).add (hv.smooth _)⟩
lemma Seen.total : sight (u+v) k=sight u k+sight v k := by ext i; rw [Poly.part_plus,sight_at,sight_at,sight_at]; exact madd (hu.smooth _) (hv.smooth _)
lemma Seen.product : Seen (u*v) := by
   constructor; intro s; simp only [Pi.mul_apply,Poly.part_mul]; refine ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => ?_
   by_cases he:Poly.merges i j s <;> simp only [he,↓reduceIte] <;> first| exact (hu.smooth _).mul (hv.smooth _) | exact contDiffAt_const
lemma Seen.paired : sight (u*v) k=∑ i∈ antidiagonal k,sight u i.1 * sight v i.2 := by
   ext s; rw [sight_at,Poly.part_sum]
   simp only [Pi.mul_apply,Poly.part_mul,sight_at]
   let f i j (x:ℝ) := if Poly.merges i j s then (u x).part i * (v x).part j else 0
   have hF (i j) : ContDiffAt ℝ ℱ (f i j) 0 := by unfold f; split <;> first| exact (hu.smooth _).mul (hv.smooth _) | exact contDiffAt_const
   rw [msum (f:=fun i x=> ∑ j,f i j x) _ (fun i _=> ContDiffAt.sum fun _ _=>hF _ _),sum_comm]; apply Finset.sum_congr rfl; intro i _
   rw [msum _ _ fun j _=> hF i j, Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _
   unfold f; by_cases he:Poly.merges i j s
   · simp only [if_pos he]; exact mprod (hu.smooth _) (hv.smooth _)
   simp only [if_neg he, mconst,ite_self,sum_const_zero]

omit hu hv in
lemma Seen.sum {ι : Type*} (V : Finset ι) (F : ι→ℝ→Poly R) (h : ∀ i∈V,Seen (F i)) : Seen (∑ i∈V,F i):= by
  induction V using Finset.induction with
  | empty=> rw [sum_empty]; exact Seen.even _
  | insert i u hi ih=>rw [sum_insert hi]; exact (h i (mem_insert_self ..)).gathers (ih (fun i hi=>h i (mem_insert_of_mem hi)))

-- power series expression by abstract smooth jet convention
omit hu hv in
def tissue (f : ℝ→Poly R) := PowerSeries.mk (sight f)
lemma Seen.adds : tissue (u+v)=tissue u+tissue v:= by ext1 i; simp_rw [tissue,map_add, PowerSeries.coeff_mk]; exact Seen.total hu hv
lemma Seen.multiplies : tissue (u*v)=tissue u*tissue v := by ext1 i; simp only [tissue,PowerSeries.coeff_mul,PowerSeries.coeff_mk]; exact Seen.paired hu hv
omit hv
lemma Seen.scales (p:ℂ) : tissue (p • u)=p • tissue u := by ext1 i; simp_rw [tissue,PowerSeries.coeff_smul, PowerSeries.coeff_mk]; exact Seen.scaled hu p
omit hu in
lemma constant_series (v : Poly R): tissue (fun _=>v)=PowerSeries.C v := by ext1 i; rw [PowerSeries.coeff_C]; unfold tissue; rw [PowerSeries.coeff_mk, sight_save]

end Shift
end YM.Comparison.RG02.Moving
