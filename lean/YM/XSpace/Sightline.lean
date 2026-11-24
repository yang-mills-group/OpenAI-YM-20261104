import YM.XSpace.Photo

/-!
# Integrations & calibration transform kept into position limit; frame metrics
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Photo
open Function Set Filter Structure1 Cirrus Normalize PowerSeries Retirement MeasureTheory Maxwell Fray
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {n:ℕ} (W:Initialize G)(V:Store G)(d:ℕ)(p:Tags G d n)(c:Shade.Cut)
lemma punct : Tendsto (fun i=> guide G d (V.layout W i d 0)) Front (𝓝 0):=by
  have ht := (V.survey d).turns_approach (V.prepared d) ((V.survey d).gait W frontier); simp_rw [Store.layout,Fray.leads]; exact ht

variable {L: Type*} {F:Filter L}
def Reads (v:L → Sec G d)(f : Sec G d): Prop:= Tendsto (fun i=> tableD G d (v i)) F (𝓝 (tableD G d f))
lemma light_cost {v:L→Change G d}{t:Change G d}(h:Tendsto (fun i=>guide G d (v i)) F (𝓝 (guide G d t)))(p:Sec G d): Reads d (F:=F) (fun i=> (v i).val p) (t.val p):=by
  let D : MoveSpace G d →ₗ[ℝ] RSpace G d:= { toFun s:= tableD G d (((guide G d).symm s).val p), map_add' s t:=by rw [map_add]; exact map_add (tableD G d) _ _, map_smul' s t:=by rw [map_smul]; exact map_smul (tableD G d) _ _ }
  have he (t:Change G d): tableD G d (t.val p)= D (guide G d t):=by simp [D]
  unfold Reads; simp_rw [he]; exact D.continuous_of_finiteDimensional.continuousAt.tendsto.comp h
lemma cue_cost (p:Sec G d): Reads d (F:=Front) (fun m=> visor W V m d p) p:=by
  have ht:= light_cost d (show Tendsto _ Front (𝓝 (guide G d (0:Change G d))) from (show Tendsto (fun i=> guide G d (V.layout W i d 0)) Front (𝓝 (guide G d 0)) by rw [map_zero]; exact punct W V d)) p; unfold Reads at *; simp only [visor,stood,map_add]; change Tendsto _ Front (𝓝 (tableD G d 0)) at ht; rw [map_zero] at ht; simpa only [add_zero] using tendsto_const_nhds (x:=tableD G d p)|>.add ht
lemma lights (v:L→Tags G d n)(he:∀ j,Reads d (F:=F) (fun i=> v i j) (p j))(B:L→ Point G d n)(T:Point G d n)(h:∀ p,Tendsto (fun i=> B i p) F (𝓝 (T p))): Tendsto (fun i=> B i (v i)) F (𝓝 (T p)):=by
  have hh (P:Point G d n)(b:Tags G d n): P b= _ := medium b (P.restrictScalars ℝ)
  simp_rw [hh (B _) (v _), hh T p]; change Tendsto _ F _; exact tendsto_finsetSum _ fun i _=>(tendsto_finsetProd _ (fun j _=> tendsto_pi_nhds.mp (he j) (i j))).smul (h _)
private lemma interior_price (f:Test n)(H:tsupport f⊆ Good c n): Tendsto (fun m=> (batchShift W m (harvest W c d m.spacing).val) n f (visor W V m d ∘ p)) Front (𝓝 (f.applyTo (fun x=> orderBasic W d c x p))):=by
  have h(q):Integrable (fun x=>f x*orderBasic W d c x q):= can_pay f (fun x=> orderBasic W d c x q) (beyond_op ..) (Senses.priced (maturation d q _ (structures W d c (n:=n)))) H (Subset.refl _)
  let P:Point G d n:= MultilinearMap.mk' (fun q=> f.applyTo fun x=> orderBasic W d c x q) (fun u i a b=> by simp_rw [Test.applyTo,MultilinearMap.map_update_add, mul_add]; exact integral_add (h _) (h _)) (fun u i a b=> by unfold Test.applyTo; simp_rw [MultilinearMap.map_update_smul,smul_eq_mul,mul_left_comm (f _) a]; exact integral_const_mul a _)
  exact lights d p (fun m=> visor W V m d ∘ p) (fun i=> cue_cost W V d (p i)) (fun m=> batchShift W m _ n f) P (fun q=> basic_test W d q c f H)

def charges (c:Shade.Cut)(x:Window G d):= x.t.applyTo (fun i=> orderBasic W d c i x.p)
def fallFee : Change G d:= -(V.survey d).tally (fun i=> charges W d c ((V.survey d).scope i))
abbrev adjustment (m:Mesh) := uproot W V m (harvest W c d m.spacing)
lemma board_paid (H:Granted V d c): Tendsto (fun i=> guide G d (adjustment W V d c i)) Front (𝓝 (guide G d (fallFee W V d c))):=by
  let K:=V.survey d; let D:= (V.measure d).D
  let U (m:Mesh):= harvest W c d m.spacing; let B(m):= batch W m d 0; let A(m:Mesh):= V.layout W m d 0
  let y i := recruit (stand (A i)) (batchShift W i (U i).val); let t i:= -D (y i); let z:=guide G d; let w i:= K.delta (K.purse (B i), z (A i)); let Z i:= adjustment W V d c i
  have S':K.Via (u:=Front) B:= K.gait W frontier; have hv i:A i=K.firstPass (V.prepared d) (B i):= Fray.leads ..
  have ht:Tendsto (fun i=> z (t i)) Front (𝓝 (z (fallFee W V d c))):=by
    have hu (j:Fin K.n): Tendsto (fun i=> watch (K.scope j) (y i)) Front (𝓝 (charges W d c (K.scope j))):= interior_price W V d (K.scope j).p c (K.scope j).t (H j)
    have h(i): z (t i)= - K.stamps (fun j=> watch (K.scope j) (y i)):=by unfold t D; rw [map_neg, ← K.equal]; rfl
    simp_rw [h]; unfold fallFee; rw [map_neg]; exact (K.stamps.continuous.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hu)).neg
  have hw:Tendsto (fun i=>(w i).inverse) Front (𝓝 1):=by simp_rw [w,hv]; exact K.toll (V.prepared d) S'
  have hh : Tendsto (fun i=>(w i).inverse (z (t i))) Front (𝓝 (z (fallFee W V d c))):= ((Continuous.clm_apply continuous_fst continuous_snd).continuousAt (x:=((1: MoveSpace G d→L[ℝ] MoveSpace G d),z (fallFee W V d c)))).tendsto.comp (hw.prodMk_nhds ht)
  apply hh.congr'; filter_upwards [((V.nested_solution W d frontier).2), show ∀ᶠ i in Front,(w i).IsInvertible from (Tendsto.prodMk_nhds S' (punct W V d)).eventually (K.unhit (V.prepared d))] with i hi he
  have h': w i (z (Z i))=z (t i) := by
    unfold w; rw [K.order, align,LinearEquiv.symm_apply_apply]; apply congr_arg; let U': Change G d:= U i; change D (tang _ _ _)=_
    have he:= hi.1.2.1 1; rw [if_neg (show (1:ℕ)≠0 from one_ne_zero)] at he; change D (V.opens W i d 1)=0 at he; rw [payment W V i U',map_add,add_comm] at he; exact eq_neg_of_add_eq_zero_left he
  exact he.inverse_apply_eq.mpr h'.symm
end YM.XSpace.Photo
