import YM.X.Tot.Stage
/-!
# Linear markers at section height. horizon slopes from advancement. Degree bound cut, storage release.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri Plate LiftMark Hinge Bare Pulse Labels Pert.RawLabels Crystal Gravity
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {F: Labels.Frames G} {q:ℕ+}{d k m l:ℕ} {V W I:Type*} {r R:ℝ} {n:Side} (p:Word G)
local notation "ε"=>epsilon q k
local notation "Q"=> flow G (side q k)
local notation "Ω"=> Label G d
variable (S:Shop F)(χ:Floor R)
def stance (S:Bare.Shop F)(q:ℕ+)(d:ℕ): Label G d→ₗ[ℂ] Foam G:= LinearMap.pi (fun k=> milk (flow G (side q k)) ∘ₗ held S (epsilon q k)⁻¹ d 0)
def splurge (q:ℕ+)(χ:Floor R)(d:ℕ)(S:Bare.Shop F)(k:ℕ) := held S (epsilon q k)⁻¹ d 1- held S (epsilon q k)⁻¹ d 0 ∘ₗ physicalLabel F d ∘ₗ (advance (k:=k) (q:=q) S χ d)
def highs (q:ℕ+)(χ:Floor R)(S:Bare.Shop F)(d:ℕ): Label G d→ₗ[ℂ] Foam G:= common S (fun p=> mature q S p χ) d -- Foam uses no hidden args
local notation "K"=> Hair G
variable (i:(F.level d).Index)
set_option quotPrecheck false
local notation "Wι"=> useWord S i
lemma earn_real (j:ℕ)(e:ℝ) : held S e⁻¹ d j ((F.level d).basis i) = mint e Wι j:= by
    rw [held_name]; unfold mint; rw [RCLike.real_smul_eq_coe_smul («K»:=ℂ)]; push_cast; rw [zpow_neg,zpow_natCast,inv_pow];rfl
lemma stanza_val (A:Ω): stance S q d A k= milk Q (held S ε⁻¹ d 0 A):=rfl
lemma stanza_name : stance S q d ((F.level d).basis i) k= milk Q (mint ε Wι 0):= by rw [stanza_val, earn_real]
lemma regal : splurge q χ d S k ((F.level d).basis i)= mint ε Wι 1-rebate q χ k Wι S:= by rw [splurge, LinearMap.sub_apply,LinearMap.comp_apply, LinearMap.comp_apply,earn_real, advance_eq, helm]
lemma high_name : highs q χ S d ((F.level d).basis i)= mature q S (Wι) χ:= common_name ..
lemma stitched : mature q S p χ k= milk Q (mint ε p 1 - rebate q χ k p S) - multi Q (milk Q (mint ε p 0)) (mask q χ k):= by
    unfold mature warp crisp matchP mint rebate mask; simp_rw [RCLike.real_smul_eq_coe_smul («K»:=ℂ),map_sub,map_smul,mscale', smul_sub,LinearMap.comp_apply]; abel
set_option maxHeartbeats 420000 in
lemma stitch (A:Ω):highs q χ S d A k=milk Q (splurge q χ d S k A) - multi Q (stance S q d A k) (mask q χ k):= by
    rw [← (F.level d).basis.sum_repr A,map_sum,map_sum,map_sum,map_sum, Finset.sum_apply,Finset.sum_apply, show multi Q _ _=((toned Q).flip (mask q χ k)) _ from rfl,map_sum,← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; rw [map_smul,high_name,Pi.smul_apply,map_smul,regal,map_smul,map_smul,Pi.smul_apply,stanza_name]; simp only [Pi.smul_apply,map_smul,← smul_sub]; exact congr_arg _ (stitched (useWord S i) S χ)
lemma raw_budget (k:ℕ)(p:Ω): duty (raw S d k p) (d/2+k):= by
    rw [← (F.level d).basis.sum_repr p,map_sum]; apply duty.costs; intro i _; rw [map_smul,raw_name]; refine duty.scalar _ (duty.more (Tri.raw_z (useWord S i)) ?_); rw [use_weight]; unfold wt; have h:= (F.level d).bound i; omega
def Cap (V:Type*)(k:ℕ): Submodule ℂ (Normal.poly V):= restrictTotalDegree _ _ k
lemma cap_ag {p:Normal.poly V}:p∈Cap V k↔ duty p k:= MvPolynomial.mem_restrictTotalDegree ..
lemma tag_stanza (p:Ω): duty (stance S q d p k) (d/2):= by rw [stanza_val]; exact (raw_budget S 0 _).milk_p _
lemma word_duty (j:ℕ): duty (milk Q (mint ε p j)) (p.d/2+j):= by unfold mint; rw [RCLike.real_smul_eq_coe_smul («K»:=ℂ)]; exact ((raw_z p).scalar _).milk_p _
lemma rebate_duty : duty (milk Q (rebate q χ k p S)) (p.d/2):= by unfold rebate;rw [RCLike.real_smul_eq_coe_smul («K»:=ℂ)]; exact ((raw_budget S 0 _).scalar _).milk_p _
lemma overflow : duty (mature q S p χ k) (p.d/2+1):= by
    rw [stitched,map_sub]; refine duty.subs (duty.subs (word_duty ..) (duty.more (rebate_duty ..) (Nat.le_succ _))) (duty.more (multi_budget (word_duty p 0) (pillar_mask χ k)) (Nat.le_succ _))
lemma stride (h:p.d=2*m):Heat.Top.cut (m+1) (mature q S p χ k)= (priceCo q (-(p.d:ℤ)) (Heat.Top.cut (m+1) (bookMark p 1))) k:= by
    rw [stitched, map_sub,map_sub, Heat.Top.cut_cap (multi ..) (Nat.lt_succ_of_le (multi_budget (k:=m) ?_ (pillar_mask χ k))), sub_zero,map_sub,Heat.Top.cut_cap (milk Q (rebate q χ k p S)) (Nat.lt_succ_of_le ?_), sub_zero, cut_thermal, mint, RCLike.real_smul_eq_coe_smul («K»:=ℂ), map_smul];
    · rfl
    · rw [mint,RCLike.real_smul_eq_coe_smul («K»:=ℂ)]; exact ((raw_z p).scalar _).more (by rw [h];omega)
    · exact (rebate_duty p S χ).more (by rw [h];omega)
    exact (word_duty ..).more (by rw [h];omega)
lemma high_apt (p:Ω)(hr:R<r)(hq:1<q.val): Apt q r (highs q χ S d p):= by
    refine ⟨⟨d/2+1,fun i=>?_⟩,fun A h=>?_⟩
    · rw [← (F.level d).basis.sum_repr p,map_sum, Finset.sum_apply]; apply duty.costs; intro j _; rw [map_smul,high_name]; apply duty.scalar; apply duty.more (overflow ..); rw [use_weight]; have h:= (F.level d).bound j; unfold wt;omega
    rw [← (F.level d).basis.sum_repr p,map_sum]; simp_rw [Finset.sum_apply,map_smul,Pi.smul_apply,map_sum,map_smul,high_name]; exact Released.sumR _ (fun i _=> breaths (constell _) (Gravity.ripe (P:=useWord S i) hq S χ hr h) ) -- order well
end YM.PositionX.Tot
