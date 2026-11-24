import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.OneLoop
import Mathlib.MeasureTheory.Integral.Prod
/-!
# LP commutation, support constraints and skeletal identities

Measure assumptions purely on loop interchange. Extend in D later. Extra
 lemmas for order-power proof. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Heat
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open scoped Topology ContDiff
variable {P I A:Type} [MeasurableSpace P] [AddCommGroup P][Fintype A]{p: Sector A}{K L: Flux A P ℂ} {F H:Row A P ℂ}(μ:Measure P){q:P}

lemma comm_Q (Z: Charge p P ℂ)(h:Pass K F μ)(hh:Pass (Z.change K) F μ)(he:closed K p false) : Z.raise (Ccy K F μ)+ Ccy (Z.change K) F μ=Ccy K (Z.raise F) μ:= by
    ext l; obtain ⟨hV,hM⟩:=cycle_map μ _ (sense_Q Z) l h; simp only [Pi.add_apply,hM]; rw [Ccy, ← integral_add hV (hh l)]; exact integral_congr_ae (Eventually.of_forall (fun q=> congr_fun (Z.commutes K he q) l)) -- check
omit [MeasurableSpace P] in
lemma each_trace {q u:P}{b c:Bool}(hx:closed K p b)(ht:closed L p c)(hk:b=false∨ c=false)(hs:Symm (field p) F): trc K u (trc L q F)=trc L q (trc K u F):= by
   classical
   have he (Z: Flux A P ℂ)(q): slab Z {q}=trc Z q:= by simp [slab]
   have hv := loop_loop (hx.balanced {u}) (ht.balanced {q}) hs; simp_rw [← is_loop, he] at hv; rcases hk with H|H <;> simpa [H] using hv
-- measure assumptions for double integration. `X→P→ℂ` order track.
lemma comm_T [SigmaFinite μ](hk:closed K p false)(hl:closed L p true)(hP:Pass K F μ)(hL: Pass L F μ)(h: Symm (field p) F)(he:∀ l, Integrable (fun u:P×P=> trc L u.1 (trc K u.2 F) l) (μ.prod μ)):
    Ccy L (Ccy K F μ) μ=Ccy K (Ccy L F μ) μ:= by
   ext l; have hK u := (cycle_map μ _ (sense_trc K u) l hL).2; have hh u := (cycle_map μ _ (sense_trc L u) l hP).2
   change (∫ u,trc L u _ l ∂μ)=∫ u,trc K u _ l ∂μ; simp_rw [hK, hh,each_trace hk hl (Or.inl rfl) h]; exact integral_integral_swap (he l)
namespace Base
-- linearity, ranks for interpolation
variable {r:ℤ}
lemma cc_equiv (hx:Agrees F H): Agrees (Ccy K F μ) (Ccy K H μ) := fun l h=> integral_congr_ae (Eventually.of_forall (fun u=> agrees_trc K u hx l h))
lemma t_add (h:Pass K F μ)(he:Pass K H μ): Pass K (F+H) μ:= by intro l; simp_rw [map_add,Pi.add_apply]; exact (h l).add (he l)
lemma cc_add (h:Pass K F μ)(he:Pass K H μ): Ccy K (F+H) μ=Ccy K F μ+Ccy K H μ:= by ext l; unfold Ccy; simp_rw [map_add,Pi.add_apply]; exact integral_add (h l) (he l)
lemma cc_scale (c:ℂ)(h: Pass K F μ): Pass K (c • F) μ:= by intro l; simp_rw [map_smul,Pi.smul_apply]; exact (h l).const_mul _
lemma ccy_s (c:ℂ): Ccy K (c • F) μ=c • Ccy K F μ:= by ext l; unfold Ccy; simp_rw [map_smul,Pi.smul_apply,integral_smul] -- expansion avoid at_trc
lemma cc_sum1 (J:Finset I){f:I→Row A P ℂ}(h:∀ i∈J,Pass K (f i) μ): Pass K (∑ i∈J,f i) μ:= by intro l; simp_rw [map_sum,Finset.sum_apply]; exact integrable_finsetSum _ (fun i hi=> h i hi l)
lemma cc_sum (J:Finset I){f:I→Row A P ℂ}(h:∀ i∈J,Pass K (f i) μ): Ccy K (∑ i∈J,f i) μ= ∑ i∈J,Ccy K (f i) μ:= by ext l; unfold Ccy; simp_rw [map_sum,Finset.sum_apply]; exact integral_finsetSum _ (fun i hi=> h i hi l)
end Base
-- tree-linear arithmetic. finite. Use sensible map for add over any real polynomial scalars. Easier prove tree as actual linearMap via `Sensible`. Maybe create `Sensible.L`. 
end YM.MS.Heat
