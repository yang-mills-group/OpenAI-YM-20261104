import YM.FrontierTrace.Shear.Frames
/-! Exact centered field conversion; scalar and offdiag for shear detector.
 Costs in this file: continuity along sparse Scaling via FirstExtension at
 zeroth order. At all positive r, algebra unconditional. -/
noncomputable section
set_option maxHeartbeats 600000
set_option autoImplicit false
namespace YM.FrontierTrace
open Function Filter Set Analysis Trace Maxwell Maxwell.Free Table
open Pert Climb UVNext.FreeStress Next.UVStress Work.A01
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace Classical

variable {G:Gauge} (L:Labels.Frames G)

lemma metric0_eq_free : metric0 L = freeStress L := by
   rw [freeStress, ← Pert.common_stress, UVNext.FreeStress.torch]
   simp only [one_smul]; rfl

lemma metric_ne_zero (h:G.Simple) : metric0 L 0 1 ≠ 0 := by
   rw [metric0,canonicalStress,if_neg (by decide : (0:Axis)≠1),sub_zero]; apply neg_ne_zero.mpr
   intro H; let t:= spin_free L
   have hv := last_pivot L t h
   unfold sightLine at hv
   rw [LinearMap.comp_apply] at hv
   have hz : ∃ e:ℂ→ₗ[ℝ] ℝ, e (hearing L (camera 0) 0 2 1 2 4 (panel L 0 1)) = -16:=⟨_,hv⟩
   obtain ⟨e,hz⟩:=hz
   rw [H,map_zero,map_zero] at hz; norm_num at hz

open Spec
variable {C:Family G} {f:Extraction.Order} {S:Table C.book}
    (F:Final C f S) (P: Spin.change S 4)

local notation "s0" => scalarLabel C.labels
local notation "T01" => metric0 C.labels 0 1
abbrev scalarA := centering S 4 (P (scalarLabel C.labels))

abbrev centered := centering S 4 (theta F 0)

lemma expectation_focus (u:S.Field 4): first_value 4 u=expectation S 4 u:=by
   rw [expectation, Work.A01.front_eval]; unfold first_value; congr 2; funext j; fin_cases j; rfl

structure Paying : Prop where
    cov : Spin.realH F.room.kernel.spin (spin_free C.labels) P
    paid_unit : P ((Model C.labels).unit 4)=S.unit 4

section frame
variable (hP : Paying F P) (hG:G.Simple)
include hP
lemma scalarA_signed (g:Signed) : S.mirror F.room.kernel.spin 4 g (scalarA P)= scalarA P := by
   rw [scalarA, mirror_center F.room.kernel]; apply congr_arg; rw [← hP.cov.1 g, scalar_signed]
lemma scalarA_real : S.conj F.room.kernel.spin 4 (scalarA P)=scalarA P:= by
   rw [scalarA, conj_center F.room.kernel]; apply congr_arg; rw [← hP.cov.2, scalar_real]
include hG
lemma scalarA_ortho (he:ExactTurns F) : ∀ g:Ortho,F.sector.turns.act 4 g (scalarA P)=scalarA P:=
    actual_ortho F he hG (scalarA_signed F P hP) (scalarA_real F P hP)
lemma scalarA_nonzero : scalarA P≠0:=by
    have h := Trace.money_ne_zero (C:=C) hG
    intro heq; unfold scalarA at heq; rw [value_center] at heq
    let u:=expectation S 4 (P s0)
    apply h
    have he: s0=u • ((Model C.labels).unit 4) := by
        apply P.injective; rw [map_smul,hP.paid_unit]; exact sub_eq_zero.mp heq
    have heS : expectation (Model C.labels) 4 s0=0:=by
       rw [scalar_as_total,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,
         show expectation (Model C.labels) _ (total C.labels)=0 from ?m, smul_zero]
       case m=> change expectation _ _ (∑ i:Axis,panel C.labels i i)=_; rw [map_sum]; simp_rw [panel_mean]; simp
    rw [he, map_smul, Next.UVStress.mean_unit (hierarchy C.labels).laws, smul_eq_mul, mul_one] at heS
    rw [he, heS,zero_smul]

lemma centered_quote (r:ℝ) : ∃ d:ℝ, r^4 • centered F = (4*d) • scalarA P := by
   let U:= (Model C.labels)
   let B:= U.unit 4
   obtain ⟨u,hu⟩:= P.surjective (theta F 0)
   let s:= F.room.kernel.spin
   obtain ⟨a,h⟩:= center_fixed_dim C.labels hG (v:=u) (fun g=> by apply P.injective; rw [hP.cov.1,hu,← F.phase.transport.spots.signed,theta_fixed]) (by apply P.injective; rw [hP.cov.2,hu,theta_real])
   let e:= expectation U 4 u
   have hg : a • scalarLabel C.labels+e • B=u := (sub_eq_iff_eq_add.mp h).symm
   have hv : theta F 0=a • P s0 + e • S.unit 4 := by
      rw [← hu,←hg,map_add,map_smul P e B,show P B = _ from hP.paid_unit,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul, RCLike.real_smul_eq_coe_smul (K:=ℂ) a (P s0)]
   refine ⟨r^4 /4*a,?_⟩; rw [centered,hv,map_add,map_smul (centering S 4) e (S.unit 4),Next.UVStress.const_out F.room.kernel.laws, smul_zero,add_zero]
   change r^4 • (centering S 4).restrictScalars ℝ (a • P s0) = _
   rw [map_smul, smul_smul,show r^4*a=4*(r^4/4*a) by ring]; rfl

-- offdiag with 0 weight mixing exactly absent. Derive using sign under individual reflection.
omit hP hG in
theorem offdia_mean {v:(Model C.labels).Field 4} (s:Signed)
    (ht : (Model C.labels).mirror (spin_free C.labels) 4 s v = -v) :
    centering (Model C.labels) 4 v=v := by
   have he: expectation (Model C.labels) 4 (-v) = expectation (Model C.labels) 4 v := by
      rw [← ht]; simp_rw [expectation,front_eval]
      let k:= Fin.cons (α:=fun _:Fin 1=>(Model C.labels).Tag) ⟨4,v⟩ (blank _)
      have he := (gear_motion C.labels) 1 k 0 conf1 s.ortho
      rw [show Points.move s.ortho (0:Points 1)=0 from PiLp.ext fun _=> map_zero (Ortho.motion _),
        show (gear C.labels).label s.ortho ∘ k = Fin.cons
          (α:=fun _ : Fin 1=> (Model C.labels).Tag) ⟨4,(gear C.labels).act 4 s.ortho v⟩ (blank _)
          from funext fun i=>by rw [Subsingleton.elim (α:=Fin 1) i 0]; rfl] at he
      rw [←(gear_laws C.labels).signed]; exact he
   rw [map_neg] at he
   have hz: expectation (Model C.labels) 4 v =0 := by
      have h:=neg_eq_iff_add_eq_zero.mp he
      -- h : etc; use module no_zero
      rw [← two_mul] at h
      exact (mul_eq_zero.mp h).resolve_left two_ne_zero
   rw [value_center,hz,zero_smul,sub_zero]

lemma offdiag_quotes (r:ℝ) : ∃ a:ℝ, ∀ (i j:Axis), i≠j →
       r^4 • F.sector.energy i j=a • P (metric0 C.labels i j) := by
   let L:= C.labels
   let t:=spin_free C.labels
   let Y:= r^(4:ℕ) • F.sector.energy
   let J:= transformed P.symm Y
   let U:= Model C.labels
   let v:= reCenter U J
   have hY: F.sector.energy ∈ SymSpace F.room.kernel.spin :=
     sym_mem.mpr ⟨F.phase.transport.conserved.symmetric,F.phase.transport.conserved.real,
      fun k i j=> by rw [← F.phase.transport.spots.signed]; exact F.phase.transport.spin ..⟩
   have hm: J∈ SymSpace (spin_free C.labels) :=
     transformed_mem (flips (⟨hP.cov.2,hP.cov.1⟩: Next.UVStress.Coherent t F.room.kernel.spin 4 P))
       ((SymSpace _).smul_mem _ hY)
   have hv : v∈KernelSpace (spin_free C.labels):= enters (hierarchy C.labels) _ hm
   obtain ⟨a,b,c,h⟩:=exhaust C.labels t hG (⟨v,hv⟩:KernelSpace _)
   refine ⟨-c,fun i j hij=>?_⟩
   have heq := congr_fun (congr_fun (show v= _ from h) i) j
   change centering _ _ (J i j)= paintStress _ _ _ _ i j at heq
   simp only [paintStress, Pi.add_apply,Pi.smul_apply,UVNext.FreeStress.across,east,west,splitDiag,
      ↓reduceIte,hij,smul_zero,add_zero,zero_add] at heq
   rw [offdia_mean (C:=C) (Signed.mirror i) ?_] at heq
   rotate_left
   · rw [tensor_column (sym_mem.mp hm).2.2]
     rw [eps_mirror_bit, eps_mirror_bit]
     norm_num [hij,Ne.symm hij,UVNext.FreeStress.bit,Signed.mirror]
   show Y i j= -c • _
   apply Eq.trans (P.apply_symm_apply (Y i j)).symm
   change P (J i j)=_
   rw [heq, RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,
     metric0,canonicalStress,if_neg hij,sub_zero,map_neg,neg_smul, smul_neg, neg_neg,
     RCLike.real_smul_eq_coe_smul (K:=ℂ)]
end frame

end YM.FrontierTrace
