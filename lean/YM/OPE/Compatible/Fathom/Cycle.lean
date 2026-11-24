import YM.OPE.Compatible.Fathom.Was
import YM.OPE.Compatible.Words.Stem
import YM.OPE.Compatible.Straws.Stoop
/-!
# Polynomial test degree and scalar IBP. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cloud
open MeasureTheory Function Set Finset Filter Module
open scoped Topology BigOperators Classical ContDiff
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial Silt
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {I J:Type}{i j k r:ℕ}
local notation "V!"=> Module.Dual ℝ E
variable {p q z:E→ℝ}
open Tensor Analysis ContinuousMultilinearMap
variable [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
variable (μ:Measure E) [μ.IsAddHaarMeasure] (A:Law E)
namespace Husk
omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in lemma laysL {i j k:ℕ}(h:Husk μ A j p)(hp:anthem k q)(ht:i+k≤ j): Husk μ A i (p*q):=⟨h.coin.mul hp.cost,fun {x} hx g hg=>by rw[mul_assoc]; exact h.pays (by omega) _ (hp.times hg)⟩
end Husk
-- Song fiscal
omit [MeasurableSpace E][BorelSpace E] in
lemma lyricCost (P:Pole E j): anthem j (Tensor.diagonal P):=by
     convert! anthem.multiline P (fun _ (x:E)=>x) (fun _=>1) (fun i l=>anthem.lyric l) using 1; simp
omit [MeasurableSpace E][BorelSpace E] in
lemma sailCost (S:Song E)(j:ℕ): anthem j (Strike j S):=by
     rw [show Strike j S=(∑ i ∈ Finset.range (j+1),diagonal (S i)) from funext fun i=>by rw[Finset.sum_apply]]; exact anthem.total _ _ fun i hi=> (lyricCost (S i)).bloat (by have ht:=mem_range.mp hi;omega)
open Cascade.Paver
variable [Fintype I] {X Y B T:Mat I} (L:E→L[ℝ] PAD I) (f:Song (PAD I))
noncomputable abbrev Expire (Z:Mat I)(S:Song (PAD I))(j:ℕ):=fixExp (opus Z) (-(1/2:ℝ)) j S
noncomputable abbrev LiftV (Z:Mat I)(S:Song (PAD I))(j:ℕ):=fixExp (opus Z) (1/2:ℝ) j S
lemma vigil (Z:Mat I)(S:Song (PAD I))(h:S∈harmon (PAD I) j): LiftV Z (Expire Z S j) j=S:=by rw [Expire, ← switching]; exact negatives (by simpa only [one_smul] using opusReducer Z 1) S h _ _ le_rfl
open Matrix
lemma eqVR (Z:Mat I)(hz: ∀ x, Health T (Z*ᵥx))(hp:∀ x, Health T x→ Z*ᵥx=x)(hP:∀ x y, Health T x→Health T y→x ⬝ᵥ(X*ᵥy)=x ⬝ᵥ(Y*ᵥy))
     (h:∀ k:ℕ,Reserve T (f k)): Expire X f j = Expire Y f j:=by
         have h1:=carriedZ (D:=Y) (M:=(1:Mat I)) (X:=X) (p:=f) (n:=j) h (show Y= _ from by simp) hz hp hP (-(1/2:ℝ)); have he(f:Song (PAD I)): pulling (1:Mat I) f=f:=by
               ext i v; change (f i) _= (f i) v; congr 1; ext1 j; exact Matrix.one_mulVec (v j)|>.trans rfl
         simpa only [he] using! h1
omit [BorelSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] in lemma eer (S: Song (PAD I))(x:Song E)(he:∀ i:ℕ, x i=(S i).compContinuousLinearMap (fun _=>L))(h:S ∈ harmon (PAD I) k): x∈ harmon E k:=by
        refine ⟨fun i hi=>?_,fun i v z=>?_⟩
        · rw[he,(show ∀ i:ℕ,i > k→S i=0 from h.1) i hi]; rfl
        rw[he]; exact h.2 i (⇑L ∘ v) z
lemma under (h:f∈ harmon (PAD I) k): Dawn μ A ((Strike k f)∘ L)= (Strike k (LiftV (Silt.chamber A L) f k)) ∘ L:=by
      funext x; have hp:=basisH μ A L (L x) 1 f h; simp only [one_smul,one_pow] at hp; unfold Dawn; simp_rw [Function.comp_apply, map_add,add_comm _ (L x)]; exact hp
-- Wick inclusion
lemma credit (Z:Mat I)(hz: ∀ x, Health T (Z*ᵥx))(hp:∀ x, Health T x→ Z*ᵥx=x)(hP:∀ x y, Health T x→Health T y→x ⬝ᵥ(X*ᵥy)=x ⬝ᵥ((Silt.chamber A L)*ᵥy))
     (h:∀ k:ℕ,Reserve T (f k))(hm:f∈ harmon (PAD I) k)(hk:∀ t:ℕ,t < i→ f t=0): Husk μ A i (Strike k (Expire X f k)∘ L):=by
          let W:=Silt.chamber A L; apply (prior (p:=Strike k (Expire X f k) ∘ L) μ A (((sailCost _ _).compLinear L.toLinearMap).cost)).mpr -- L coerces?
          intro j hj; rw [eqVR _ Z hz hp hP h,under μ A L (Expire W f k) (peak _ _ _ _ hm),vigil _ f hm]
          let Y:Song E:= fun i=>(f i).compContinuousLinearMap (fun _=>L); rw [show Strike k f ∘ L=Strike k Y from funext fun i=>rfl, gradeC (eer L _ Y (fun _=>rfl) hm)]; unfold Y; rw[hk j hj];rfl
lemma bursary (h:f∈ harmon (PAD I) k)(H:Surjective L): (Husk μ A i (Strike k f ∘ L)) ↔ ∀ j:ℕ,j < i→LiftV (Silt.chamber A L) f k j=0:=by
       let F:= LiftV (Silt.chamber A L) f k; let Y:Song E:=fun j=> (F j).compContinuousLinearMap (fun _=>L); have hp:Y ∈ harmon E k:=eer L F Y (fun _=>rfl) (peak _ _ _ _ h); have ht(j:ℕ): Tensor.coeff (Dawn μ A (Strike k f ∘ L)) j 0= Y j:=by rw [under μ A L f h]; exact gradeC hp j
       rw[prior (p:=Strike k f ∘ L) μ A (show Bond _ from ((sailCost f k).compLinear L.toLinearMap).cost)]; simp_rw [ht]; constructor
       · intro hi j hj; ext1 v; choose p hp using fun i:Fin j => H (v i); change F j v=_; rw[show v= (fun i=>L (p i)) from (funext hp).symm]; exact DFunLike.congr_fun (hi j hj) p
       intro hi j hj; unfold Y F; rw[hi j hj];rfl
end YM.OPE.Cloud
