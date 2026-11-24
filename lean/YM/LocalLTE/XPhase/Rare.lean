import YM.LocalLTE.XPhase.Closure
import YM.MergeProof.Close
/-!
# Carrying mixed attachments from regular analytic mask movements
across singular projection. Keep the concrete positions branch by branch.
Fugacity reserve consumed only after the closure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.XPhase
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open MergeProof MergeProof.Accent GridApprox.Nil Extra.Trajectories
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
variable {w: V→ℝ} {F H: I→ Y→Poly B} {X:I→Support n} {b:ℕ}{d C C' t:ℝ}
lemma loci_combine {F H:Y→Poly B}(he:Loci w F t)(hx:Loci w H C):Loci w (F-H) (t+C):=by
    obtain ⟨a,ha,h,hz⟩:=he; obtain ⟨c,hc,hH,hV⟩:=hx; refine ⟨fun i=>a i+c i,fun i=>add_nonneg (ha i) (hc i),fun i j=>?_,?_⟩
    · rw [Pi.sub_apply,part_sub]; exact (norm_sub_le ..).trans (add_le_add (h i j) (hH i j))
    unfold wordsPrice; simp_rw [mul_add,Finset.sum_add_distrib]; exact add_le_add hz hV
lemma towed_difference (he:Towed w X F b d C)(hv:Towed w X H b d C'):Towed w X (F-H) b d (C+C'):=by
    obtain ⟨a,ha,h,hA⟩:=he; obtain ⟨c,hc,hp,hC⟩:=hv
    refine ⟨fun i=>a i+c i,ha.add hc,fun x=>?_,fun i=>loci_combine (hA i) (hC i)⟩
    convert! Local.sumBudget_add (h x) (hp x) using 2; rename_i i; split <;> ring
lemma crew [Fintype I][Fintype J]{g:J→Y→Poly B}{s:J→Support n}(he:Towed w X F b d C)(hv:Towed w s g b d C'):Towed w (Sum.elim X s) (Sum.elim F g) b d (C+C'):=by
    obtain ⟨a,ha,h,hA⟩:=he; obtain ⟨c,hc,hp,hC⟩:=hv
    refine ⟨Sum.elim a c,Summable.of_finite,fun x=>?_ , fun i=> ?_⟩
    · refine ⟨fun i=> ?_,Summable.of_finite,?_⟩; cases i; exact (h _).1 _; exact (hp _).1 _
      rw [tsum_fintype,Fintype.sum_sum_type]; let h:= (h x).2.2; let h':=(hp x).2.2; -- with rewriting
      have hQ:=add_le_add h h'; rw [tsum_fintype,tsum_fintype] at hQ; exact hQ
    cases i; exact hA _; exact hC _
lemma bolder {F H: Config G n→ Poly B}{o:V→Site n}{p q:Support n}(hf:Borne o p F t)(hH:Borne o q H t)(hx:p⊆q): Borne o q (F-H) t:=by
    refine ⟨fun U V h ht=> congr_arg₂ (·-·) (Work.H03.reads_larger hx hf.home U V h ht) (hH.home U V h ht),fun g U=> congr_arg₂ (·-·) (hf.turns g U) (hH.turns g U),fun i=>?_,fun U i hi=>?_⟩
    · simp_rw [Pi.sub_apply,Extra.Trajectories.part_sub]; exact (hf.me _).sub (hH.me _)
    change (F U-H U).part i=0; rw [part_sub,hH.scope _ _ hi,hf.scope _ _ (fun h=>hi (h.trans (fun _ hi=>hx hi))),sub_zero]
section
variable [Fintype J] [Fintype V]
variable (f:J→ Config G n→Poly B) (S:J→ Support n) (hw: ∀ i,0<w i)
abbrev Rising (B:Census V):= {i:B.Mode//2 ≤ i.val.card}
def packer : Rising B × J→ Config G n→Poly B:= fun i U=> Poly.send i.1.val ((f i.2 U).part i.1.val)
-- correct argument order.
omit [Fintype V] in
lemma packed {U:Config G n}(he:∀ i,rises (f i U)) : (∑ i: Rising B × J,packer f i U) = ∑ i,f i U:=by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _=>?_ ; let g (i:Rising B):= i.val
    change ∑ i:Rising B,Poly.send (g i) ((f j U).part (g i))=f j U
    let P:=(f j U); have hP(i)(hp: i ∉ Set.range g): P.part i=0:=Classical.byContradiction (fun h=> hp ⟨⟨_,he j _ h⟩,rfl⟩)
    refine Eq.trans ?_ (Poly.studs (f j U)); rw [← tsum_fintype (L:=SummationFilter.unconditional _)]
    rw [← tsum_fintype (L:=SummationFilter.unconditional _)]; apply (show Injective g from Subtype.val_injective).tsum_eq (f:=fun i=> Poly.send i ((f j U).part i)); intro i hi; by_contra h; apply hi; change Poly.send i _=0; rw [show (f j U).part i=0 from hP i h]; exact Poly.send_zero _
variable {o:V→Site n} (hf:∀ j,Borne o (S j) (f j) t)(ht:∀ j U,rises (f j U))
include hf
omit [Fintype V] [Fintype J] in
lemma pack_b (i:Rising B × J): Borne o (S i.2) (packer f i) t:=by
    let s:=i.1.val; let g V:=(f i.2 V); let q:=(o)
    refine ⟨fun U V h' ht=> congr_arg (fun p:Poly B=> Poly.send s (p.part s)) ((hf _).home U V h' ht),fun g' U=> congr_arg (fun p:Poly B=> Poly.send s (p.part s)) ((hf _).turns g' U),fun j=> ?_,fun U k hZ=> ?_⟩
    · simp_rw [packer,Poly.part_send]; split; exact (hf i.2).me _; exact measurable_const
    rw [packer,Poly.part_send]; split; next he=>rw [← he]; exact (hf _).scope U k hZ
    rfl
omit hf
include hw
lemma pack_ledger (h:Towed w S f b d C): Towed w (S ∘ Prod.snd) (packer f) b d C:=by
    obtain ⟨a,ha,hA,h⟩:=h; choose e he hP hE using h
    let m(i:Rising B × J):= Poly.toll w i.1.val*e i.2 i.1.val; have hp i:0 ≤ m i:= mul_nonneg (Poly.worth hw _|>.le) (he _ _)
    refine ⟨m,Summable.of_finite,fun i=> ?_,fun i=> satin (fun U=> (f i.2 U).part i.1.val) i.1.val _ (he _ _) (fun U=> hP _ _ _)⟩
    refine ⟨fun i=> ?_,Summable.of_finite,?_⟩
    · dsimp only; split; next x=> exact mul_nonneg (hp _) (Real.exp_nonneg _)
      next=> rfl
    have h := (hA i).2.2; rw [tsum_fintype] at h; rw [tsum_fintype,Fintype.sum_prod_type, Finset.sum_comm]; refine le_trans (Finset.sum_le_sum (fun j hj=>?_)) h
    by_cases hn: i∈S j; swap
    · simp only [Function.comp_apply,hn,↓reduceIte,Finset.sum_const_zero,le_refl]
      -- Lean may normalize
    simp only [Function.comp_apply,hn,↓reduceIte];rw [← Finset.sum_mul]; refine mul_le_mul_of_nonneg_right ((le_trans ?_ (hE j))) (Real.exp_nonneg _)
    let f':= fun (i:B.Mode) => Poly.toll w i * e j i; have hz: Finset.univ.image (Subtype.val (p:=fun i:B.Mode=>2 ≤ i.val.card)) ⊆ Finset.univ:= Finset.subset_univ _
    have he := Finset.sum_le_sum_of_subset_of_nonneg (f:=f') hz (fun i _ _=>mul_nonneg (Poly.worth hw _|>.le) (he _ _)); rw [sum_image (show Set.InjOn (Subtype.val) _ from Subtype.val_injective.injOn)] at he; exact he
end
end YM.LocalLTE.XPhase
