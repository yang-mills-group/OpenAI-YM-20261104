import YM.Frontier6.Forest.Render.Array

/-! Uniform pricing errors permit questions asked independently. No geometry
 constant dependence retained past reaching the detector expenses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Forest.Flare
open Road Function Set Finset Filter Fareway Spec Tale
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {I V X:Type}{G:Gauge}{C:Family G}{H:Extraction.Order}{S:Table C.book}{T:Fareway I}{b a c p q t:ℝ}
variable [Fintype V][DecidableEq V][Fintype X][DecidableEq X]
variable (K:Final C H S)(F:V→ Spark S I)(A:X→ Spark S I)
attribute [local instance] Spark.ft Spark.de Spark.ne
set_option quotPrecheck false
local notation "F'"=> Sum.elim F A
lemma shine_joint {P Q:Fabric I} (h:∀ i,(F i).Shine T b P)(he:∀ j,(A j).Shine T b Q) : ∀ w:V⊕X,(Sum.elim F A w).Shine T b (P⊔Q):=by rintro (i|j); exacts [(h i).extends extends_left,(he j).extends extends_right]
lemma homes_join {P Q:Fabric I} (h:∀ i,(F i).Shine T b P)(he:∀ j,(A j).Shine T b Q)(hx:Wide T (home F) a)(hy:Wide T (home A) a)(hr:Cross T P Q a): Wide T (home (F')) a:=by
    have hp : ∀ i,home (F') i=Sum.elim (home F i) (home A i):= by intro i; ext1 j;cases j <;> rfl
    exact Wide.cf (unity hx hy (fun i j=> hr.wide ((h i).lives) ((he j).lives))) (Eventually.of_forall (fun i=> (hp i).symm))
lemma levy_join (p q:ℝ): levy (F') p q= levy F p q+levy A p q:=by unfold levy; rw [Fintype.sum_sum_type]; rfl
abbrev fleet (x:I→ X→ E4)(v:X→ S.Tag):= fun i:X=> Spark.lone (fun k=>x k i) (v i)
variable (h:Road.Ribbon C H S) {F}{P:Fabric I}
def levy_fleet {I:Type}(v:X→ S.Tag)(p q:ℝ):ℝ:=levy (fleet (I:=I) (fun i x=>0) v) p q -- unused
include h
set_option maxHeartbeats 600000 in
lemma fleets (w:ℝ) (v:X→ S.Tag)(hC:0<b)(he:∀ i,(F i).Shine T b P)(hf:Wide T (home F) a)(ha:a<b)(hp:p<b): ∀ᶠ d:ℕ in atTop, Query T P K v (showAt F-shared K F d) w p:= by
    let t:=max a p/b; have ht:b*t=max a p:= by unfold t; field_simp -- inspect
    have he':t<1:= (div_lt_one hC).mpr (max_lt_iff.mpr ⟨ha,hp⟩)
    obtain ⟨c,hc,hc'⟩:= exists_between (max_lt he' zero_lt_one); obtain ⟨q,hq,hq'⟩:= exists_between hc'; obtain ⟨r,hr,hr'⟩:= exists_between hq'; have he'':t<c:= (le_max_left ..).trans_lt hc; have hZ:0<c:= (le_max_right ..).trans_lt hc
    let x:=levy F q r+levy_fleet (I:=I) v q r; let w':= x-w/b
    filter_upwards [eventually_all.mpr (fun i:X=> eventually_ge_atTop ((v i).fst)), (Tendsto.atTop_mul_const (r:=(r-q)^2) (pow_pos (sub_pos.mpr hr) _) tendsto_natCast_atTop_atTop).eventually_ge_atTop w'] with d hd hM y hy hP s -- typo eventual define
    let A:= fleet y v; have hA(i:X):(A i).Shine T b (sheet y):= Spark.shines_lone (v i) (contains_sheet y i)
    have hu: p ≤ b*t:= ht.symm ▸ le_max_right ..
    have hz:Wide T (home (Sum.elim F A)) (b*t):= homes_join F A he hA (hf.higher (ht.symm ▸ le_max_left ..)) (hy.higher hu) (hP.scale hu) -- hx defeq
    have hp':= cost_wall K h (shine_joint F A he hA) hz hC he'' hZ hq hr hr' d s
    rw [levy_join, show levy A q r=levy_fleet (I:=I) v q r from rfl, showAt_join, shared_join] at hp'
    have htA:showAt A=inscription S y v:=by ext1 i; unfold showAt A fleet; simp_rw [Spark.real_lone];rfl
    rw [htA] at hp'
    apply (hp'.too (show b*(x-d*(r-q)^2) ≤ w by unfold w' at hM; rw [mul_comm b]; apply (le_div_iff₀ hC).mp; linarith)).cf
    filter_upwards with i; unfold polled; rw [Pi.sub_apply,Pi.mul_apply,Pi.mul_apply,Pi.mul_apply,Pi.sub_apply,sub_mul,map_sub,map_sub]
    congr 1; apply Tale.Congr.done K; apply Tale.Congr.left K; apply Tale.Congr.product K (V:=X); intro j hj; change Tale.Congr K (all K _ _ ((Spark.lone _ (v j)).real i)) _; rw [Spark.real_lone]; exact letter_all K d _ (v j).snd (hd j)
end YM.Frontier6.Forest.Flare
