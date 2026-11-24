import YM.OPE.Levy.Panel

/-! # The weak-frame inverse has a nonperturbative engineering bound

Use two-point measurements and the exact reflection symmetries of this
particular extraction. The measured radius may be a sparse trajectory; in
particular this uses no running-coupling matching assumption. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Levy
open Set Filter Function Pert Orbits Spec Table Extraction Ward Climb Next.UVStress
open Push.FiniteDetection.Free Maxwell
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical ComplexOrder
variable {G:Gauge}{C:Family G}{f:Order}{S:Table C.book}(h:Final C f S)(d:ℕ) (X:Scaling S)(H:FirstExtension h X)
local notation "ρ" => h.room.kernel.spin
local notation "U" => X.U
def bar (v:S.Field d): S.Field d := S.mirror ρ d (Signed.mirror timeAxis) (S.conj ρ d v)

include H
lemma column (x:S.Field d):∃ c:ℝ,0<c ∧ ∀ᶠ n in atTop, ‖(U n d).symm x‖^2 ≤ c*‖pair d S (X.r n • detectors) x (bar h d x)‖:=by
   obtain ⟨a,ha,hf⟩:=norm_test h d X H
   refine ⟨a,ha,?_⟩
   filter_upwards [H.fit.hsym d, hf] with n hn ht
   have he(a):U n d (reflect d a)=bar h d (U n d a):=(hn.1 (Signed.mirror timeAxis) _).trans (congr_arg (S.mirror ρ d _) (hn.2 _))
   specialize ht ((U n d).symm x)
   convert ht using 1
   change _ = a*‖pair (S:=S) d S _ (U n d _) (U n d (reflect ..))‖
   rw [he,LinearEquiv.apply_symm_apply]

set_option quotPrecheck false
def meter (X:Scaling S)(k:ℕ):= -Real.log (X.r k)
local notation "T" => meter X

section
omit H
lemma meter_big: Tendsto (meter X) atTop atTop:=
    Filter.tendsto_neg_atTop_iff.mpr (Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨X.drips,Eventually.of_forall X.positive⟩))
lemma meters(i): X.r i = Real.exp (-1 * meter X i):=(by rw [meter,neg_mul_neg,one_mul,Real.exp_log (X.positive i)])

variable {I:Type}[Fintype I]{z:I→E4} (x:ℕ→I→E4)(hz:Injective z)(hx: x= fun i j=> X.r i • z j)
include hz hx
lemma zoom_kept: Kept atTop T 1 x:=by
   intro p hp
   have he (i j:I): ∀ᶠ k in atTop, i≠j → Real.exp (-p*T k)< ‖x k i-x k j‖:=by
     by_cases ht:i=j
     · exact Eventually.of_forall fun k hu=> (hu ht).elim
     have hh:= (RateIs.exp (-1) (meter_big X)).mul (RateIs.const (meter_big X) (norm_sub_pos_iff.mpr (hz.ne ht)))
     filter_upwards [hh.overtakes (RateLE.exp (-p) (meter_big X)) (meter_big X) (by linarith)] with k hk hk'
     rw [hx]; dsimp; rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (X.positive k),meters]; exact hk
   exact eventually_all.mpr fun i=>eventually_all.mpr fun j=>he i j

omit hz hx [Fintype I]
theorem two_size : Fintype.card (Unit ⊕ Unit)=2 :=by simp
private abbrev transMap: Unit⊕Unit≃Fin 2 := ((runNames _).symm.trans (Equiv.cast (congr_arg Fin two_size)))
private abbrev render (x:Fin 2→E4):Unit⊕Unit→E4 :=x∘ transMap
private abbrev submit (v:Fin 2→S.Field d): Labels S (fun _:Unit⊕Unit=>d) := fun j=>v (transMap j)
private lemma refresh {b:ℕ}{w:b=2}(x:Fin 2→ E4)(v:Fin 2→S.Field d): S.useAt S (points (x∘ (Fin.cast w)))
        (fun i:Fin b=>⟨d,v (Fin.cast w i)⟩)=S.useAt S (points x) (fun i=>⟨d,v i⟩) :=by subst b; rfl
private lemma common_cast {b:ℕ}(w:b=2)(i:Fin b):Equiv.cast (congr_arg Fin w) i=Fin.cast w i:=by subst b; rfl
private lemma disk (x: Fin 2→ E4)(v u:S.Field d):pair d S (points x) v u = observe S (render x) (names (submit d ![v,u])):=by
   rw [← Orbits.observed]; unfold pair Orbits.moment
   have ht(i:Fin (Fintype.card _)):transMap (runNames (Unit⊕Unit) i)=Fin.cast two_size i :=
       (congr_arg (Equiv.cast (congr_arg Fin two_size)) ((runNames _).symm_apply_apply i)).trans (common_cast two_size i)
   have he:(render x ∘ runNames (Unit⊕Unit))= x ∘ (Fin.cast two_size):= funext fun i=> congr_arg x (ht _)
   have hs(i:Fin (Fintype.card (Unit⊕Unit))): submit d ![v,u] (runNames (Unit ⊕ Unit) i)= ![v,u] (Fin.cast two_size i):=congr_arg ![v,u] (ht i)
   change _=S.useAt S (points _) _
   rw [he]
   refine Eq.trans (refresh d (w:=two_size) x ![v,u]).symm (congr_arg _ ?_)
   exact funext fun i=> congr_arg _ (hs i).symm
include h
lemma fixed_pair (ht:Services C f S)(v u:S.Field d):RateLE atTop T (fun i=>pair d S (X.r i • detectors) v u) (d+d:ℝ):=by
   let x(i:ℕ):=render ((X.r i • detectors):Points 2).ofLp
   have hb:Kept atTop T 1 x:= zoom_kept X x ((show Injective detectors.ofLp from detectors_in).comp (transMap.injective)) rfl
   let v':= submit d ![v,u]; let C':=Unit⊕Unit
   let a(x:C'→E4):=x ∘ Sum.inl; let b(x:C'→E4):=x ∘ Sum.inr
   have hK (f:Unit→C')(hf:Injective f):Kept atTop T 1 (fun i=>x i∘ f):=by
       intro b hu; filter_upwards [hb b hu] with i hi j j' hj using hi _ _ (hf.ne hj)
   have hp:Intervals atTop T 1 (a∘x) (b∘x):=by intro t ht; filter_upwards [hb t ht] with i hi j j' using hi (.inl _) (.inr _) (Sum.inl_ne_inr)
   have hg:= viewer_cost h ht.schedule (names v' ∘ Sum.inl) (names v' ∘ Sum.inr) (meter_big X) (fun _=>none) (hK Sum.inl Sum.inl_injective) (hK Sum.inr Sum.inr_injective) hp zero_le_one le_rfl
   convert hg using 1
   · funext i; exact (disk d _ _ _).trans (by unfold x v' OPE.spectator; apply congr_arg₂ (OPE.observe S) (funext (fun q=>by cases q <;> rfl)) (funext (fun q=>by cases q <;> rfl)))
   unfold OPE.sigma Orbits.names v'; simp [submit]
end

open OPE.Nesting
include H
theorem inverse_subpower (ht:Services C f S)(u:S.Field d):RateLE atTop T (fun i=>(U i d).symm u) (d:ℝ):=by
   obtain ⟨c,hc,hK⟩:=column h d X H u
   have hw:RateLE atTop T (fun i => pair d S (X.r i • detectors) u (bar h d u)) (d+d:ℝ):=fixed_pair h d X ht _ _
   intro a ha
   filter_upwards [hK,hw (a+d) (by linarith), (RateIs.const (meter_big X) hc |>.pays (meter_big X)) (a-d) (by linarith)] with i h1 h2 h3
   rw [Real.norm_eq_abs,abs_of_pos hc] at h3
   have ee: Real.exp (a*T i)^2 = Real.exp ((a-d)*T i) * Real.exp ((a+d)*T i):= by rw [pow_two,← Real.exp_add,←Real.exp_add]; congr 1; ring
   have hh:=h1.trans (mul_le_mul h3 h2 (norm_nonneg _) (Real.exp_pos _).le)
   nlinarith only [hh,ee,Real.exp_pos (a*T i),norm_nonneg ((U i d).symm u)]

end YM.OPE.Levy
