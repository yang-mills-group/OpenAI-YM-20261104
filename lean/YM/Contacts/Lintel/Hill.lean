import YM.Contacts.Lintel.Wire
namespace YM.Contacts.Lintel
set_option linter.unusedSectionVars false
open Function Set Finset Filter Metric RG Wilson Lattice Precision Exterior MeasureTheory
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F05
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open PertExtension.Chart Radial
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{c f m: Side}{α:ℕ→Type}{n k:ℕ}
variable {V X Y E:Type}[NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V]
   [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {t:E} {a b:E→ ℝ}
namespace Crag
open Wire
local notation "Α" => E × V
variable {M F K J:(E × V)→ℝ}
structure Paired (F M K J:(E × V)→ℝ):Prop where
   core: AnalyticAt ℝ F 0
   axis: AnalyticAt ℝ M 0
   K0: AnalyticAt ℝ K 0
   J0: AnalyticAt ℝ J 0
   spin: spiral M=M
   spinJ: spiral J=J
   canyon (v:V) : avoid M v 2
   will (v:V): avoid (F-M) v 3
   delta (v:V): avoid (K-J) v 1
   gap: ∃ c:ℝ,0<c ∧ ∀ v:V,c*‖v‖^2 ≤ jet M 2 (0,v)
variable (h:Paired F M K J)
lemma serenity {f:E→ℝ}(h:AnalyticAt ℝ f 0)(hk:∀ x,jet f 0 x=0)(hx:∀ x,jet f 1 x=0): Radial.Stationary f:= ⟨h.contDiffAt, jet_zero f 0 ▸ hk (0:E), hx⟩
namespace Paired
variable {h}
lemma g_comp (h:Paired F M K J)(x:E)(y:V)(k:ℕ)(hk:k≤2) : jet F k (x,y)=jet M k (x,y):= sub_eq_zero.mp ((Ion.jet_minus F M k (x,y) h.core h.axis |>.symm).trans (evade_jet (h.core.sub h.axis) (h.will y) x k (by omega))) -- args
lemma old (h:Paired (E:=E) (V:=V) F M K J): Radial.Stationary M:= serenity h.axis (fun ⟨x,y⟩=>evade_jet h.axis (h.canyon y) x _ (by omega)) (fun ⟨x,y⟩=>evade_jet h.axis (h.canyon y) x _ (by omega))
lemma new (h: Paired (E:=E) (V:=V) F M K J): Radial.Stationary F := serenity h.core (fun ⟨x,y⟩=> (h.g_comp x y 0 (by decide)).trans ((jet_zero ..).trans h.old.base0)) (fun ⟨x,y⟩=> (h.g_comp x y 1 (by decide)).trans (h.old.base1 _))
lemma base_eq (h: Paired (E:=E) (V:=V) F M K J) (v:E) (z:V): kernel F (v,z)=kernel M (0,z):= congr_arg (fun y=>Real.exp (-y)) ((h.g_comp v z 2 le_rfl).trans (seed h.axis (h.canyon z) v)) -- syntax
lemma slants (h:Paired (E:=E) (V:=V) F M K J)(R:ℝ): ∃ c>0, ∃ C,Hilly F (c+c) R C ∧ Hilly M (c+c) R C:= by
   obtain ⟨c,hc,H⟩:= h.gap; refine ⟨c/2, by positivity, c*R^2, fun x hx v=>?_, fun x hx v=>?_⟩; · rw [h.g_comp x v _ le_rfl, seed h.axis (h.canyon v) x]; have hx:= mem_closedBall_zero_iff.mp hx; rw [Prod.norm_def]; cases le_total ‖x‖ ‖v‖ <;> rename_i hz; rw [max_eq_right hz]; nlinarith only [H v,mul_nonneg hc.le (sq_nonneg R)]; rw [max_eq_left hz]; nlinarith only [mul_nonneg hc.le (sq_nonneg ‖v‖),H v,mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx 2) hc.le]
   rw [seed h.axis (h.canyon v) x, ← h.g_comp 0 v _ le_rfl]; rw [h.g_comp 0 v _ le_rfl]; have hx:= mem_closedBall_zero_iff.mp hx; rw [Prod.norm_def]; cases le_total ‖x‖ ‖v‖ <;> rename_i hz; rw [max_eq_right hz]; nlinarith only [H v,mul_nonneg hc.le (sq_nonneg R)]; rw [max_eq_left hz]; nlinarith only [mul_nonneg hc.le (sq_nonneg ‖v‖),H v,mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx 2) hc.le]
lemma K_init (h:Paired (E:=E) (V:=V) F M K J): K 0= J 0 := by have he:= evade_jet (h.K0.sub h.J0) (h.delta 0) 0 _ zero_lt_one; rw [jet_zero] at he; exact sub_eq_zero.mp he
end Paired
-- moment matching by parity. zero kernel common, first antisymmetric, second discrepancy of symmetric evaluations independent of x.
private lemma ad0 : (HasAntidiagonal.antidiagonal 0 : Finset (ℕ×ℕ))={(0,0)}:= by ext ⟨i,j⟩; simp
private lemma ad1 : (HasAntidiagonal.antidiagonal 1 : Finset (ℕ×ℕ))={(0,1),(1,0)}:= by ext ⟨i,j⟩; simp [HasAntidiagonal.mem_antidiagonal]; omega
private lemma ad2 : (HasAntidiagonal.antidiagonal 2 : Finset (ℕ×ℕ))={(0,2),(1,1),(2,0)}:= by ext ⟨i,j⟩; simp [HasAntidiagonal.mem_antidiagonal]; omega
lemma theme0 (a:E→ℝ)(b:E→ℝ)(x:E): integrandSeries a b 0 x=b 0:= by norm_num [integrandSeries, Radial.layers, Zone.mul, Zone.TaylorPow,expsum, Finset.sum_range_succ,ad0,ad1,ad2]
lemma theme1 (a:E→ℝ)(b:E→ℝ)(x:E): integrandSeries a b 1 x=jet b 1 x-b 0*jet a 3 x:= by norm_num [integrandSeries, Radial.layers, Zone.mul, Zone.TaylorPow,expsum, Finset.sum_range_succ,ad0,ad1]; ring
lemma theme2 (a:E→ℝ)(b:E→ℝ)(x:E): integrandSeries a b 2 x=jet b 2 x- jet b 1 x*jet a 3 x+ b 0*((jet a 3 x)^2/2-jet a 4 x):= by norm_num [integrandSeries, Radial.layers, Zone.mul, Zone.TaylorPow,expsum, Finset.sum_range_succ,ad0,ad1,ad2]; ring
private lemma rise (F:(E × V)→ℝ)(h: spiral F=F)(ht:AnalyticAt ℝ F 0)(k:ℕ) (x:E)(z:V): jet F k (x,-z)=jet F k (x,z):= by  exact (lat_jet _ ht (n:=k) (x,z)).symm.trans (by rw [h])
private lemma twist (a: E→ℝ)(k:ℕ)(hk:Odd k)(x:E): jet a k (-x)= -(jet a k x):= by rw [← neg_one_smul ℝ x,jet_smul, hk.neg_one_pow]; ring
include h
lemma hymn (i:ℕ) (hi:i ≤ 1) (x:E)(v:V): normTerm K F i (x,v)+normTerm K F i (x,-v)=normTerm J M i (x,v)+normTerm J M i (x,-v):= by
   have he (v:V): kernel M (x,v)= kernel M (0,v):= congr_arg (fun y=>Real.exp (-y)) (seed h.axis (h.canyon v) x); have hp: kernel M (0,-v)=kernel M (0,v):= congr_arg (fun y=>Real.exp (-y)) (rise _ h.spin h.axis 2 0 v);
   unfold normTerm; rw [h.base_eq, h.base_eq, he, he, hp]; interval_cases i;
   · simp_rw [theme0, h.K_init];
   simp_rw [theme1,h.K_init]; let z:(E × V):=(0,v); have hu (k:ℕ): (0,-v)=-z:= Prod.ext neg_zero.symm rfl; have hs (y:V):= seed (h.core.sub h.axis) (h.will y) x; have hw (y:V):= seed (h.K0.sub h.J0) (h.delta y) x;
   rw [← add_mul,← add_mul]; congr 1; set ξ:= J 0; have hI : jet K 1 (x,v)+jet K 1 (x,-v)=jet J 1 (x,v)+jet J 1 (x,-v):= by
      have he:= hw (-v); have hh:= hw v; rw [hu 1,twist _ 1 ⟨0,rfl⟩] at he
      simp_rw [Ion.jet_minus K J _ _ h.K0 h.J0] at he hh; unfold z at *; linarith only [he,hh]
   rw [sub_add_sub_comm,sub_add_sub_comm,← mul_add,←mul_add,hI]; apply congr_arg; apply congr_arg; have he:= hs (-v); have hh:= hs v; rw [hu 3,twist _ 3 ⟨1,rfl⟩] at he; simp_rw [Ion.jet_minus F M _ _ h.core h.axis] at he hh; unfold z at *; linarith only [he,hh]
lemma total_second (x:E)(v:V): normTerm K F 2 (x,v)+normTerm K F 2 (x,-v)-(normTerm J M 2 (x,v)+normTerm J M 2 (x,-v))=2*(normTerm K F 2 (0,v)-normTerm J M 2 (0,v)):= by
   let z: E×V:=(0,v); let p: E×V:=(x,v); let q: E×V:=(x,-v); have hu : (0,-v)=-z:=Prod.ext neg_zero.symm rfl; have he(v:V): kernel M (x,v)=kernel M (0,v):= congr_arg (fun y=>Real.exp (-y)) (seed h.axis (h.canyon v) x); have hp : kernel M (0,-v)=kernel M (0,v):= congr_arg (fun y=>Real.exp (-y)) (rise _ h.spin h.axis 2 0 v)
   unfold normTerm; rw [h.base_eq x v,h.base_eq x _,h.base_eq 0 v,he v,he (-v),hp,←add_mul,←add_mul,←sub_mul,←sub_mul,←mul_assoc]; congr 1; set u:= J 0;
   let K' := K-J; let F':=F-M; have hK (w: E×V)(i:ℕ): jet K i w=jet J i w+jet K' i w:= by unfold K'; rw [Ion.jet_minus _ _ _ _ h.K0 h.J0]; ring; -- semicolon
   have hT (w: E×V) (i:ℕ): jet F i w=jet M i w+jet F' i w:= by unfold F'; rw [Ion.jet_minus _ _ _ _ h.core h.axis]; ring
   have hy : jet J 1 (0,v)=0:= by have hh:= rise _ h.spinJ h.J0 1 0 v; rw [hu, twist _ 1 ⟨0,rfl⟩] at hh; unfold z at *; linarith only [hh]
   have ht : jet M 3 (0,v)=0:= by have hh:= rise _ h.spin h.axis 3 0 v; rw [hu, twist _ 3 ⟨1,rfl⟩] at hh; unfold z at *; linarith only [hh]
   let a:= jet K' 1 (0,v); let b:=jet F' 3 (0,v); have h₁ (v:V): jet K' 1 (x,v)=jet K' 1 (0,v):= seed (h.K0.sub h.J0) (h.delta v) _; have h₂ (v:V): jet F' 3 (x,v)=jet F' 3 (0,v):= seed (h.core.sub h.axis) (h.will v) _
   have hA:= spare (h.K0.sub h.J0) v ⟨0,rfl⟩ (h.delta v) x; have hB:= spare (h.core.sub h.axis) v (k:=3) ⟨1,rfl⟩ (h.will v) x; change jet K' 2 (x,v)+jet K' 2 (x,-v)=2*jet K' 2 (0,v) at hA; change jet F' 4 (x,v)+jet F' 4 (x,-v)=2*jet F' 4 (0,v) at hB
   have hb: jet K' 2 (x,-v)=2*jet K' 2 (0,v)-jet K' 2 (x,v):=eq_sub_of_add_eq' hA; have hb': jet F' 4 (x,-v)=2*_ -jet F' 4 (x,v) :=eq_sub_of_add_eq' hB; simp_rw [theme2,h.K_init,hT,hK,rise _ h.spin h.axis _ x v, rise _ h.spinJ h.J0 _ x v]; rw [h₁ v,h₁ (-v),h₂ v,h₂ (-v),hb,hb',hy,ht,hu,twist _ 3 ⟨1,rfl⟩,twist _ 1 ⟨0,rfl⟩]; unfold z; ring
-- integration against μ using reflection
variable [MeasurableSpace E][MeasurableSpace V][BorelSpace E][BorelSpace V]
variable (μ:Measure V)[μ.IsNegInvariant][μ.HasTemperateGrowth]
include μ
omit h [μ.HasTemperateGrowth] in
private lemma both (f:V→ℝ)(h:Integrable f μ): Integrable (fun x=> f x+f (-x)) μ ∧ (∫ x,f x+f (-x) ∂μ)=2*∫ x,f x ∂μ:= by
   let η: V≃ₜ V:=Homeomorph.neg _; let e:=η.toMeasurableEquiv; have hp:MeasurePreserving e μ μ:= Measure.measurePreserving_neg μ;
   have he: (∫ x,f (-x) ∂μ)=∫ x,f x ∂μ:= hp.integral_comp' _; have hh : Integrable (fun x=>f (-x)) μ:= hp.integrable_comp_emb e.measurableEmbedding|>.mpr h
   exact ⟨h.add hh,(integral_add h hh).trans (by rw [he]; ring)⟩
lemma bridal (x:E)(i:ℕ)(hi:i≤1): mural μ K F i x=mural μ J M i x:= by
   obtain ⟨c,hc,C,hF,hM⟩:= h.slants ‖x‖; have hx:x∈closedBall 0 ‖x‖:= mem_closedBall_zero_iff.mpr le_rfl; let f:=fun y=> normTerm K F i (x,y); let m:=fun y=> normTerm J M i (x,y); have ht:= (both μ f (termInt μ h.new h.K0.contDiffAt hc hF hx i)).2; have hu:= (both μ m (termInt μ h.old h.J0.contDiffAt hc hM hx i)).2; apply mul_left_cancel₀ (two_ne_zero' ℝ); exact ht.symm.trans ((integral_congr_ae (Eventually.of_forall fun t=> hymn h i hi x t)).trans hu)
lemma breeze (x:E): mural μ K F 2 x -mural μ J M 2 x=mural μ K F 2 0 -mural μ J M 2 0:= by
   let S (x:E)(v:V):=normTerm K F 2 (x,v)-normTerm J M 2 (x,v); let T (x:E):= fun v:V=>S x v+S x (-v); let e:=∫ v: V,S 0 v ∂μ; have he x : T x= (fun y=> 2*S 0 y):= funext fun v=> ((sub_add_sub_comm ..).trans (total_second h x v))
   have hp x : mural μ K F 2 x-mural μ J M 2 x=e:= by
      obtain ⟨c,hc,C,hF,hM⟩:= h.slants ‖x‖; have hx:x∈closedBall 0 ‖x‖:= mem_closedBall_zero_iff.mpr le_rfl; have ht:= termInt μ h.new h.K0.contDiffAt hc hF hx 2; have hu:=termInt μ h.old h.J0.contDiffAt hc hM hx 2
      unfold Milling.mural; rw [← integral_sub ht hu]; apply mul_left_cancel₀ (two_ne_zero' ℝ); change 2*(∫ v,S x v ∂μ)=_; rw [← (both μ (S x) (ht.sub hu)).2, ← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall fun v=> congr_fun (he x) v)
   exact (hp x).trans (hp 0).symm
end Crag
end
end YM.Contacts.Lintel
