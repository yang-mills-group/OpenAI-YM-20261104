import YM.Frontier6.Forest.Render.Mist

/-! Render estimates (also center cap against compact satellite family). -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Forest
open Road Function Set Finset Filter Fareway Spec Tale
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {I V X:Type}{G:Gauge}{C:Family G}{H:Extraction.Order}{S:Table C.book}{T : Fareway I}{b a:ℝ} {P:Fabric I} {A:Art S I} {x:I→ E4}
variable (K:Final C H S) (h:Road.Ribbon C H S)
lemma scalar_cost (X:Type*) [NormedAddCommGroup X][NormedSpace ℂ X] {c:I→ℂ}{f:I→X}(he:T.Costs c a)(hp:T.Costs f b): T.Costs (fun i=> c i • f i) (a+b):=he.coordinated hp _ (Eventually.of_forall fun i=> (norm_smul ..).le)
namespace Mist
include h
lemma colorless (hc:b=0)(s:I→ StateIndex K) (he:Mist T b P A a): T.Costs (polled K s A) a:=by
   induction he with
   | word v hx hP=> apply (crude K h.grill hx hc.ge v s).too; rw [hc]; simp
   | add _ _ ha hb=> apply (ha.add hb).cf; exact Eventually.of_forall fun i=>(map_add (poll S _) _ _).symm
   | scale hc hh ih=> refine (hc.coordinated ih _ (Eventually.of_forall fun i=>?_)); unfold polled; rw [map_smul,norm_smul]
   | cf _ hk ih=> exact ih.cf (hk.mono fun i hi=> congr_arg (poll S _) hi)
   | mono _ he ih=> exact ih.too he
   | zero=> exact Costs.free.cf (Eventually.of_forall fun _=>(map_zero (poll S _)).symm)
lemma query_away (hc:b=0)(he: Mist T b P A a)[Fintype V][DecidableEq V](v:V→ S.Tag): Query T P K v A a 0:=by
    intro y hy hf s; subst b; cases isEmpty_or_nonempty V
    case inl hV =>
        simp only [show inscription S y v=1 from funext fun i=> by unfold inscription assembly; rw [Finset.univ_eq_empty,Finset.prod_empty]; rfl, mul_one]; exact he.colorless K h rfl s
    case inr HV=> have ht:= word v hy (P:= sheet y) (Forest.Extends.rfl (sheet y)); simpa only [mul_zero,add_zero] using (he.multiplication ht hf).colorless K h rfl s
lemma painted (hh:Mist T b P A a)(he:Local T P x b)(hc:0<b)(d:ℕ): T.Costs (fun i=> pitch K (x i) d (A i)) (a-d*b):=by
    have ht:= he.ready K hc d
    induction hh with
    | word v hx hp=>
       have hz:= pin_physical K h x v hx (fun i=>he.cost (hp.contains (contains_sheet _ i))) hc d (Fin.last d)
       apply Fareway.Costs.too _ (show b*(load v-d) ≤ load v*b - (d:ℝ)*b from le_of_eq (by ring))
       refine hz.cf (Eventually.of_forall fun i=>?_); unfold reach pitch; dsimp only [Fin.val_last,inscription]; exact congr_arg _ (projects_self K _)
    | add hv hp hL hH=>
       refine (hL.add hH).cf ?_; filter_upwards [lights K d ht hv.acts, lights K d ht hp.acts] with i hi he using (pitch_plus K _ _ _ hi he).symm
    | @scale c k w Z hh hX ih=> apply (scalar_cost _ hh ih|>.too (show k+(w-d*b)≤_ from le_of_eq (by ring))).cf; exact (lights K d ht hX.acts).mono fun i hi=>(pitch_scal K _ _ _ (c i) hi).symm
    | cf h hh ih=> exact ih.cf (hh.mono fun i hi=> congr_arg (pitch K _ _) hi)
    | mono h hh ih=> exact ih.too (by linarith only [hh])
    | zero=> exact Costs.free.cf (Eventually.of_forall fun i=>(pitch_void K _ (x i)).symm)
lemma relevant (hh:Mist T b P A a)(he:Local T P x b)(hc:0≤b)(d:ℕ)(hr:Forest.Centered T P x K d): T.Costs (fun i=> pitch K (x i) d (A i)) (a-d*b):=by
    rcases eq_or_lt_of_le hc with hh'|hh'; swap; exact painted K h hh he hh' _
    rw [hh'.symm,mul_zero,sub_zero]; exact (moonlit K hr (lights K d hr hh.acts) (fun _ _ _ z=> hh.query_away K h hh'.symm _)).mapped (weight K d)
omit h
lemma suits (d:ℕ)(v:I→ S.Field d)(hx:Contains T P x)(he:T.Costs v a): Mist T b P (fun i=>suit K (x i) d (v i)) (a+(d:ℝ)*b):=by
    simp_rw [suit_eq]; refine folds _ (fun y _=> scale ?_ (step ⟨d,(marker K d y).val⟩ hx)); exact he.mapped (LinearMap.toContinuousLinearMap ((marker K d).coord y ∘ₗ face K d))
lemma lower_ready (K: Final C H S){d w:ℕ}(ht:Forest.Centered T P x K d)(he:w≤d):Forest.Centered T P x K w:= by obtain ⟨r,hr,hp,h⟩:=ht; exact ⟨r,hr.down K he le_rfl,hp,h⟩
include h
lemma dye (hh:Mist T b P A a)(he:Local T P x b)(hc:0≤b)(d:ℕ)(ht:Forest.Centered T P x K d)(hx:Contains T P x): Mist T b P (fun i=> reject K (x i) d (A i)) a:=by
    have hp(w:ℕ)(hw:w≤d): Mist T b P (fun i=> part K (x i) w (A i)) a:= (suits K w _ hx (relevant K h hh he hc _ (lower_ready K ht hw))).mono (w:=a-w*b+w*b) (by exact (sub_add_cancel ..).le)
    refine Mist.sub hh ?_ -- defeq?
    exact (folds (b:=b) (V:=Fin (d+1)) Finset.univ (fun w _=> hp w (Nat.lt_add_one_iff.mp w.isLt))).cf ((lights K d ht hh.acts).mono fun i hi=>(all_from_parts K d (x i) _ hi).symm)
end Mist
end YM.Frontier6.Forest
