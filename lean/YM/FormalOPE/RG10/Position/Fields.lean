import YM.FormalOPE.RG10.Position.Mint

/-!
# Common formal coefficient limit in positioned WilsonX **before** mass-independent adjustment
Consumption of the missing RG08/09/06/11 inputs (precise below). Operates for **all** smooth
profiles with their indicated field basis and real combination rule, on ALL horizons. Nontrivial
proofs of horizon/restriction/calibration identities at these general limits. No assumption of
convergence of an infinite power series nor assertion that the controller demands are uniform over
profiles, orders, horizons, scale or q. Additional rates and controller choice independence on
moving RG schedule required for actual comparison. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Position
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle Peal Plan
open scoped Topology BigOperators ContDiff Classical

/-- Use a common cofinal controller for all comparison requests; e.g. choose a divisibility
progression of sufficiently large odd aux blocks. No limit $q→∞$ is taken of any correlation:
instead each sufficiently large block in this filter must give the *same* requested answer. -/
structure Drivers where
  ages : Filter ℕ+
  ne : ages.NeBot
  cofinal : ages ≤ atTop
  big : ∀ᶠ q in ages, 1 < q.val
  odd : ∀ᶠ q in ages, Odd q.val
attribute [instance] Drivers.ne
variable {G : Gauge} {F : Frames G} {j k n d : ℕ}
local notation "M" d => Mark (Deck F d) Profile.n

namespace Drivers
variable (Y : Drivers) {R:Type*}[TopologicalSpace R]
def Harvest (x: ℕ+ → ℕ → R) (A:R) := ∀ᶠ q in Y.ages, Tendsto (x q) atTop (𝓝 A)
def Credit (x: ℕ+ → ℕ → fps) (A : fps) := ∀ i, Y.Harvest (fun q n=>coeff i (x q n)) (coeff i A)
variable {Y}
lemma Harvest.ext [T2Space R]{x : ℕ+→ℕ→R} {A B:R} (h:Y.Harvest x A)(k:Y.Harvest x B):A=B :=
    let ⟨_,hu,hv⟩:= (h.and k).exists; tendsto_nhds_unique hu hv
lemma Harvest.const (a:R): Y.Harvest (fun _ _=>a) a:= Eventually.of_forall (fun _=>tendsto_const_nhds)
lemma Harvest.along {a b:R}{x y:ℕ+→ℕ→R} (h:Y.Harvest x a) (hb:a=b)(hu:∀ᶠ q in Y.ages, ∀ᶠ i:ℕ in atTop, x q i=y q i) : Y.Harvest y b := by
  unfold Harvest; filter_upwards [h,hu] with q h he; rw [← hb]; exact h.congr' he
lemma Credit.accepts {x : ℕ+→ℕ→fps} {A B:fps}(h:Y.Credit x A)(k:Y.Credit x B):A=B:= by ext i : 1; exact (h i).ext (k i)
lemma Credit.permanent (a:fps):Y.Credit (fun _ _=>a) a:= fun _=>Harvest.const _
namespace Credit
variable {x y:ℕ+→ℕ→fps} {A B:fps} (h:Y.Credit x A)(hk₂:Y.Credit y B)
include h hk₂
lemma added : Y.Credit (x+y) (A+B):=by intro i; unfold Harvest; filter_upwards [h i,hk₂ i] with a hu hk;
                                                                   simpa using! hu.add hk
lemma product : Y.Credit (x*y) (A*B):=by
 intro i; unfold Harvest; let S:= Finset.HasAntidiagonal.antidiagonal i
 have he := eventually_all_finset S |>.mpr (show ∀ s∈S,Y.Harvest _ (coeff s.1 A) from fun s _=> h s.1) -- placeholders
 have hf := eventually_all_finset S |>.mpr (show ∀ s∈S,Y.Harvest _ (coeff s.2 B) from fun s _=> hk₂ s.2)
 filter_upwards [he,hf] with q h₁ h₂; simp_rw [Pi.mul_apply,coeff_mul]; exact tendsto_finsetSum _ fun s hs=>(h₁ s hs).mul (h₂ s hs)
omit hk₂ in
lemma neg : Y.Credit (-x) (-A):=by intro i; unfold Harvest; filter_upwards [h i] with a ha;
                                                   simpa using! ha.neg
omit h hk₂
lemma sum {I:Type*}{x:I→ℕ+→ℕ→fps}{A:I→fps}(s:Finset I)(u:∀ i∈s,Y.Credit (x i) (A i)): Y.Credit (∑ i∈s,x i) (∑ i∈s,A i):=by
 induction s using Finset.induction_on with
 | empty=> rw [Finset.sum_empty,Finset.sum_empty]; exact permanent 0
 | insert i S h ih=> rw [sum_insert h,sum_insert h]; exact added (u i (by simp)) (ih (fun a ha=>u a (by simp [ha])))
lemma prod {I:Type*}{x:I→ℕ+→ℕ→fps}{A:I→fps}(s:Finset I)(u:∀ i∈s,Y.Credit (x i) (A i)): Y.Credit (∏ i∈s,x i) (∏ i∈s,A i):=by
 induction s using Finset.induction_on with
 | empty=> rw [Finset.prod_empty,Finset.prod_empty]; exact permanent 1
 | insert i S h ih=> rw [prod_insert h,prod_insert h]; exact product (u i (by simp)) (ih (fun a ha=>u a (by simp [ha])))
lemma summons {I:Type*}{x:I→ℕ+→ℕ→fps}{A:I→fps}(s:Finset I)(u:∀ i∈s,Y.Credit (x i) (A i)): Y.Credit (fun q i=>∑ j∈s,x j q i) (∑ j∈s,A j):= by simpa only [← Finset.sum_apply] using sum s u
lemma times {I:Type*}{x:I→ℕ+→ℕ→fps}{A:I→fps}(s:Finset I)(u:∀ i∈s,Y.Credit (x i) (A i)): Y.Credit (fun q i=>∏ j∈s,x j q i) (∏ j∈s,A j):= by simpa only [← Finset.prod_apply] using prod s u
include h
lemma cut : Y.Credit (fun q i=> Triangle.deviation (x q i)) (Triangle.deviation A) := by
 have hc (a:fps)(i) : coeff i (Triangle.deviation a)=if i=0 then 0 else coeff i a := by
   unfold Triangle.deviation; rw [map_sub,coeff_C]; split <;> rename_i H <;> simp [H]
 intro i; simp_rw [hc]; split <;> rename_i H
 · exact Harvest.const _
 exact h i
include hk₂
lemma folded : Y.Credit (fun q i=> x q i + y q i) (A+B):= added h hk₂
lemma or_less :Y.Credit (fun q i=>x q i - y q i) (A-B):= by
  simpa only [sub_eq_add_neg] using! folded h (neg hk₂)
lemma cartesian : Y.Credit (fun q i=> x q i * y q i) (A*B):= product h hk₂
omit h hk₂

end Credit
namespace Tasks
variable {a : (Mark (Deck F 6) Profile.n)→ℕ+→ℕ→fps} {A : (Mark (Deck F 6) Profile.n)→fps} (h:∀ v:(Mark (Deck F 6) Profile.n),Y.Credit (a v) (A v))
include h
set_option maxHeartbeats 200000 in
lemma taps {n} (x : Fin n ↪ Fin 3) : Y.Credit (fun q i=> Peal.touch F (fun j=> a j q i) x) (Peal.touch F A x):=by
  let v:=(⟨n,Peal.near x⟩: Profile)
  let u (i:Fin n→ Deck F 6):= (⟨v,i⟩:Mark (Deck F 6) Profile.n)
  let p (z:Fin n→ Deck F 6):= PowerSeries.C (∏ i,tune F (x i) (z i))
  exact Credit.summons (x:=fun (i:Fin n→ Deck F 6) q k=> p i * a (u i) q k) (A:=fun i=>p i*A (u i)) univ (fun i _=>Credit.cartesian (Credit.permanent (p i)) (h (u i)))
set_option maxHeartbeats 200000 in
lemma collected : Y.Credit (fun q i=>mint F (fun j=>a j q i)) (mint F A) := by
 let t := fun n (x:Fin n ↪ Fin 3) q i=> Peal.touch F (fun j=> a j q i) x
 have hx : Y.Credit (fun q i=>∑ k:Fin 3,t 2 k.succAboveEmb q i * t 1 (Peal.single k) q i)
      (∑ k:Fin 3, Peal.touch F A k.succAboveEmb * Peal.touch F A (Peal.single k)) :=
    Credit.summons (x:=fun (k:Fin 3) q i=> t 2 k.succAboveEmb q i * t 1 (Peal.single k) q i) (A:=fun k=>touch F A k.succAboveEmb * touch F A (Peal.single k)) univ (fun k _=> Credit.cartesian (taps h k.succAboveEmb) (taps h (Peal.single k)))
 have hv : Y.Credit (fun q i=>∏ k:Fin 3,t 1 (Peal.single k) q i) (∏ k:Fin 3, Peal.touch F A (Peal.single k)) := Credit.times (x:=fun (k:Fin 3) => t 1 (Peal.single k)) (A:=fun k=>touch F A (Peal.single k)) univ (fun k _=> taps h (Peal.single k))
 have hb : Y.Credit (fun q i=>together F (fun j=>a j q i)) (together F A) := Credit.folded (Credit.or_less (taps h (.refl _)) hx) (Credit.cartesian (Credit.permanent 2) hv)
 exact Credit.cartesian (Credit.permanent (C ((slope G)⁻¹))) hb.cut
end Tasks
end Drivers

-- meaningful rate-free continuum hypothesis on each distinct arity and slice BEFORE OPE,
-- despite the need for additional estimates in degenerating geometry. Include openness.
structure Patience (P:Plan F)(Y:Drivers) : Prop where
  certified : Official P.stock
  funding : ∀ᶠ q in Y.ages, Tendsto (fun m => coeff 1 (together F (P.dressed q m 6))) atTop (𝓝 (slope G))
  panel (d k:ℕ) (v: Mark (Deck F d) Profile.n) : ∃ A:ℝ,Y.Harvest (fun q m=> coeff k (Plan.collect F P q m d v)) A
namespace Patience
variable {P:Plan F} {Y : Drivers}(Z:Patience P Y)

def Yield (v:M d) : fps:= PowerSeries.mk fun i=>(Z.panel d i v).choose
lemma collected (v:M d) : Y.Credit (fun q m=>Plan.collect F P q m d v) (Z.Yield v) := by intro i; rw [Yield,coeff_mk]; exact (Z.panel d i v).choose_spec
lemma leading (v:M d) : constantCoeff (Z.Yield v) = Physical.free (L:=Maxwell.standard F) (deck F d) v := by
 apply (show Y.Harvest _ _ from ?_).ext (Y:=Y) (x:=fun q m=>constantCoeff (Plan.collect F P q m d v)) (Y.big.mono fun i hi=>Plan.listening Z.certified hi v)
 simpa only [coeff_zero_eq_constantCoeff_apply] using Z.collected v 0

lemma larger (hk:d ≤ k) (v:M d) : Z.Yield (ascend Profile.n (Deck.climb F hk) v)= Z.Yield v:= by
 ext i:1
 apply (Z.collected _ i).ext
 exact (Z.collected v i).along rfl (Y.big.mono fun q hq=> (Plan.accumulate Z.certified hq hk).mono (fun n h=>congr_arg (coeff i) (congr_fun h v))) -- along direction

lemma ordering : (P.stock d).select (fun v=> coeff k (Z.Yield (markIn _ v))) = if k=0 then (P.stock d).target else 0 := by
 let s:=P.stock d
 let x(q:ℕ+)(m:ℕ) : s.Z:= s.select (fun v=>coeff k (collect F P q m d (markIn _ v)))
 refine Drivers.Harvest.ext (Y:=Y) (x:=x) ?_ ?_
 · have hk := Filter.eventually_all.mpr (show ∀ v: Questionnaire (J:=Deck F d) (arity:=Profile.n) s.tests, Y.Harvest _ (coeff k (Z.Yield (markIn _ v))) from fun v=> Z.collected _ k)
   unfold Drivers.Harvest; filter_upwards [hk] with q hC
   exact s.select.continuous_of_finiteDimensional.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hC)
 apply Drivers.Harvest.along (Y:=Y) (Drivers.Harvest.const _) rfl
 filter_upwards [Y.big] with q hq; filter_upwards [Plan.objectives (d:=d) Z.certified hq] with m he; exact (he k).symm

lemma calibration (h:G.Simple) : mint F (fun v=>Z.Yield (d:=6) v)=X := by
 have he:= (Drivers.Tasks.collected (a:=fun v q m=>Plan.collect F P q m 6 v) (fun v=>Z.collected (d:=6) v))
 refine he.accepts ?_
 intro i; apply Drivers.Harvest.along (Drivers.Harvest.const _) rfl
 filter_upwards [Z.funding] with q hq;
 filter_upwards [hq.eventually (isOpen_compl_singleton.mem_nhds (pulse (G:=G) h |>.ne'))] with m hm
 exact congr_arg (coeff i) ((Plan.uses_axis (F:=F) P m h hm).symm)
end Patience
end YM.FormalOPE.RG10.Position
