import YM.MS.Arts.Shuttle
/-!
# Commutation raising and projecting PX cycle (ordinary Lebesgue)

Integrable assumptions real and enough to conclude pilot preservation. No
 D catalog here. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts.Pilot
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open scoped Topology ContDiff
variable {A B R P:Type}[Fintype A][CommRing R][AddCommGroup P]{p: Koszul.Sector A}
variable {K:Pilot R P p} {X Y:Charge p P R}
def Counts (K:Pilot R P p)(X Y:Charge p P R): Prop:=∀ i a b,(∑ j,X.table a j i*K.fieldC j b)= ∑ j,K.fieldC a j * Y.table j b (K.volp i)
namespace Counts
variable (h:Counts K X Y)
include h
lemma port (F) (a:A)(q:P): X.move.hook (a,q) (beam K F)= ∑ i,K.fieldC a i • beam K (Y.move.hook (i,K.volp q) F):= by
    simp_rw [Charge.hook_rule _ _,map_sum,map_smul,served,Finset.smul_sum, smul_smul]; conv_rhs=> rw [Finset.sum_comm ]
    rw [Finset.sum_comm]; simp_rw [← Finset.sum_smul, h q]
lemma walk (F): beam K (Y.raise F)= X.raise (beam K F):= by
   funext l; induction l generalizing F with
   | nil=> simp [Charge.raise]
   | cons i l ih=> simp only [D_eval i]; rcases i with ⟨a,q⟩; unfold Charge.raise at *; simp only [served, Shift.deriving',map_add, map_sum,map_smul,Finset.smul_sum, smul_add,Finset.sum_add_distrib, port h, Pi.add_apply,Finset.sum_apply,Pi.smul_apply, ih]; congr 1; apply Finset.sum_congr rfl; intro c hc; by_cases hp:K.fieldC a c=0; simp [hp]; dsimp only [field]; rw [K.pair_zero a c hp]; exact smul_comm ..
end Counts
variable [MeasurableSpace P]
open Submodule
variable (K:Pilot ℂ P p){X Y: Flux A P ℂ} {μ:Measure P}
omit [Fintype A] [AddCommGroup P] [MeasurableSpace P] in
lemma portD (k:Mode A P) (W:(Row A P ℂ)→ℂ)(h:W∈ Heat.Centre (Legs (Mode A P))): (fun F=>W (D k F))∈ Heat.Centre (Legs (Mode A P)):= by
    refine Submodule.span_induction (p:=fun V _=> (fun F=> V (D k F))∈ Heat.Centre (Legs (Mode A P))) ?_ (by exact (Heat.Centre _).zero_mem) ?_ ?_ h -- use Centre.. 
    · rintro u ⟨i,rfl⟩; exact Heat.centroid _
    · intro i j hx hy he hq; exact cent_add _ _ he hq
    intro c i hx he; exact cent_scale _ _ he
omit [MeasurableSpace P] in
lemma sense : Sensible K.beam:= by
   refine ⟨fun l=>?_⟩; induction l with
   | nil=> simp_rw [peeps]; exact centroid ([]:List (Mode A P))
   | cons i l ih=> simp_rw [met]; exact cent_sum _ _ (fun a _=> cent_scale _ _ (portD _ _ ih)) -- infer K unused
lemma leadC (h: MeasurePreserving K.volp μ μ)(hh:MeasurableEmbedding K.volp)(hK:K.Transport X Y)(F:Row A P ℂ)(hy:Pass Y F μ): beam K (Ccy Y F μ)=Ccy X (beam K F) μ:= by
   funext l; rw [(cycle_map μ _ (sense K) l hy).2,← h.integral_comp hh (fun q=>beam K (trc Y q F) l)]; simp_rw [hK.shuttle0]
end YM.MS.Arts.Pilot
