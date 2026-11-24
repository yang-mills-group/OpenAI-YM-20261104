import YM.Frontier6.Multi.Tale.Letters

/-! Smooth on endpoints, translation and covariance from off-C. -/
set_option autoImplicit false
noncomputable section
set_option quotPrecheck false
namespace YM.Frontier6.Tale
open Function Filter Set Finset Spec
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {V X:Type*}[Fintype V][TopologicalSpace X] {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K: Final C F S)(s:StateIndex K)
local notation "T"=>state K s
local notation "E"=>(Fintype.equivFin V).symm

lemma acast (z:V→S.Tag)(y:V→ E4) : poll S T (assembly S y z)=if Injective y then S.useAt T (points (y ∘ (Fintype.equivFin V).symm)) (z ∘ (Fintype.equivFin V).symm) else 0:= remap S T y z _ _ rfl (hierarchy K s).laws.toSymmetric
lemma larger {f:X→V→ E4}{x:X}(hc:ContinuousAt f x)(h:Injective (f x)) :∀ᶠ i in 𝓝 x, Injective (f i):=by
    -- equivalent through points
    let z:X→ Points (Fintype.card V):=fun x=> points (f x ∘ (E))
    have hz: ContinuousAt z x:=by unfold z points; exact (PiLp.continuous_toLp ..).continuousAt.comp (f:=fun x=>f x ∘ E) (by exact continuousAt_pi.mpr (fun j=> (continuous_apply (E j)).continuousAt.comp hc)) -- FFD
    have hv:z x∈ conf (Fintype.card V):= h.comp (E).injective
    filter_upwards [hz.eventually ((conf_open _).mem_nhds hv)] with i hi; exact (Equiv.injective_comp E (f i)).1 hi
lemma assembly_cont {f:X→V→ E4}{x:X}(hc:ContinuousAt f x)(h:Injective (f x))(z:V→ S.Tag): ContinuousAt (fun i=>poll S (state K s) (assembly S (f i) z)) x :=by
   let p:X→Points (Fintype.card V):=fun x=> points (f x ∘ (E))
   have hp:ContinuousAt p x:=by unfold p points; exact (PiLp.continuous_toLp ..).continuousAt.comp (f:=fun x=>f x ∘ E) (by exact continuousAt_pi.mpr (fun j=> (continuous_apply (E j)).continuousAt.comp hc))
   refine ((((S.class_smooth T (hierarchy K s).smooth _).continuousOn.continuousAt ((conf_open _).mem_nhds (show p x∈ conf (Fintype.card V) from h.comp (E).injective))).comp hp)).congr (f:=fun y=> S.useAt T (p y) (z∘E)) (?_) -- test
   filter_upwards [larger hc h] with i hi; rw [acast,if_pos hi] -- orientation
lemma translating (a:E4)(z:V→S.Tag)(x:V→ E4): poll S (state K s) (assembly S (fun i=> x i+a) z)=poll S (state K s) (assembly S x z):=by
   have he:Injective (fun i=>x i+a) ↔ Injective x:=by simp [Injective];
   rw [acast,acast]; simp only [he]; split
   next h=> exact use_across K s (x:=points (x ∘ E)) (h.comp (E).injective) (z ∘ E) a
   rfl
-- weathered normal costs with external hierarchy
end YM.Frontier6.Tale
