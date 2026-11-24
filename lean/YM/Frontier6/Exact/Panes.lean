import YM.Frontier6.Exact.Words
import YM.Work.A13
import YM.Work.A12
import YM.Frontier6.Exact.Dual
import Mathlib.Topology.Baire.Lemmas

/-! Bypass link-tile seams for the fusion measurement by a true O(4)
rotation, also in the chosen phase. Independent of angles in the pair itself. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6
open Function Filter Set Lattice Wilson RG Source Labels MergeProof MergeProof.Ribbons Next.UVStress
open Bid Spec Analysis Table Extraction.Lease Cells Extraction.Around OS Word MeasureTheory Org Canvas Platform
open Next.Extract Dash PhysicalNext.Repeat.Legato MergeProof.Acme
open scoped Topology InnerProductSpace BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order} {S:Table C.book}
variable (K:Final C F S)

open Work.A13
local instance : CompactSpace Ortho:= Work.A12.compact_ortho
private lemma seam_avoided (x:E4)(i:Axis)(r:ℝ)(hr:r≠0):
   IsOpen {u:Ortho| Ortho.move u x i≠r} ∧ Dense {u:Ortho| Ortho.move u x i≠r}:=by
   refine ⟨isOpen_ne_fun (g:=fun _=>r) ?_ continuous_const,fun u=> ?_⟩
   · simp_rw [Ortho.move,M4.at_coord]
     exact continuous_finsetSum _ fun j _=> (show Continuous (fun k:Ortho=> k.val i j) from (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)).mul continuous_const
   refine mem_closure_iff_frequently.mpr (?_)
   intro he
   have hU:∀ᶠ v in 𝓝 u, Ortho.move v x i=r:= he.mono (fun v hv=>not_ne_iff.mp hv)
   have hv := hU.self_of_nhds
   obtain ⟨j,hj⟩:= exists_ne i
   let y:= Ortho.move u x; let V (t:ℝ):= Ortho.oneParameter (Ortho.plane i j) t
   have ht:Tendsto V (𝓝 0) (𝓝 1):=by
      rw [← oneParameter_zero (Ortho.plane i j)]; apply tendsto_subtype_rng.mpr
      exact (hasDerivAt_exp_smul_const' (Ortho.plane i j).val (0:ℝ)).continuousAt
   let f(t:ℝ):=Real.cos t*y i+Real.sin t*y j
   have hV: f =ᶠ[𝓝 0] fun _=>r:=by
      have h: Tendsto (fun t=> V t * u) (𝓝 0) (𝓝 u):=by simpa using ht.mul_const u
      filter_upwards [h.eventually hU] with i' hi
      change Ortho.move (V i' * u) x i=r at hi; rw [Ortho.move_mul,(plane_givens (Ne.symm hj) _ _).1] at hi; exact hi
   have hp : AnalyticOnNhd ℝ f univ:= fun x _=> by
      unfold f; exact (Real.analyticAt_cos.mul analyticAt_const).add (Real.analyticAt_sin.mul analyticAt_const) -- check
   have hz : f Real.pi=r:= hp.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const isPreconnected_univ (mem_univ _) hV (mem_univ _)
   have he : y i=r:=hv
   simp only [f,Real.cos_pi,Real.sin_pi,zero_mul,neg_mul,one_mul,add_zero,he] at hz; apply hr; linarith
lemma rotates_zero (R:Ortho) : Ortho.move R 0=0:= (Ortho.motion R).map_zero
lemma rotates_cons {n:ℕ} (R:Ortho)(x:E4)(y:Points n): Points.move R (Points.cons x y)=Points.cons (Ortho.move R x) (Points.move R y):=by ext1 i; refine Fin.cases ?_ (fun j=>?_) i <;> rfl
lemma clear_rotates {n:ℕ} (R:Ortho)(p:ℝ)(x:Points n)(hc:clearC p x): clearC p (Points.move R x):=by
   unfold clearC; rw [show (Points.cons 0 (Points.move R x))= Points.move R (Points.cons 0 x) from ((rotates_cons R 0 x).trans (by rw [rotates_zero])).symm] -- syntax specify
   intro i j hij; let y:=Points.cons 0 x; change p < ‖Ortho.motion R _- Ortho.motion R _‖; rw [← map_sub,(Ortho.motion R).norm_map]; exact hc i j hij

variable {I:Type*}[Fintype I]{n:I→ℕ}(Y:Schedule)(b:ℕ)
def revolve (s:Ortho)(y:Seen n) : Seen n:= fun i=> Points.move s (y i)
lemma towards (y:Seen n) {a:ℝ}(hs:shapes a y)(hp:4*Y.a b ≤ a): ∃ (s:Ortho)(g:ℝ),0 < g ∧ noSeam Y b g (revolve s y):=by
    let U (j:(Σ i:I, Fin (n i)) × Axis × ℤ) := {s:Ortho| Ortho.move s (y j.1.1 j.1.2) j.2.1≠ Y.a b*(j.2.2-1/2)}
    have ht (z:ℤ): Y.a b *((z:ℝ)-1/2) ≠ 0:=by
       refine mul_ne_zero (Y.a_pos _).ne' fun h=>?_; have hz: (2:ℤ)*z=1:=by exact_mod_cast (show (2:ℝ)*z=1 by linarith)
       omega
    obtain ⟨s,H⟩:= (dense_iInter_of_isOpen (f:=U) (fun i=> (seam_avoided _ _ _ (ht _)).1) (fun i=> (seam_avoided _ _ _ (ht _)).2)).nonempty
    let T:= revolve s y; let C (i:I)(j:Fin (n i))(a:Axis):ℤ:=⌊T i j a / Y.a b+1/2⌋
    have he (i j v): |T i j v-Y.gridPoint b (C i j) v| < Y.a b/2:= by
       let f:= Y.a b; let t := T i j v; let z := C i j v; let u:= t/f+1/2
       have hf:0<f:=Y.a_pos _
       have hr : ¬ t=f*((z:ℝ)-1/2):= mem_iInter.mp H ((⟨i,j⟩,v,z) : (Σ i:I, Fin (n i)) × Axis × ℤ)
       have ht : ↑z ≤ u:= Int.floor_le u; have hx:u< z+1:=Int.lt_floor_add_one u; have hh:t/f*f=t:=div_mul_cancel₀ _ hf.ne'
       change |t-f*(z:ℝ)|<f/2; unfold u at *
       have hv:= (lt_or_gt_of_ne hr); rcases hv with hl|hl
       · exfalso; linarith only [hl,mul_le_mul_of_nonneg_right ht hf.le,hh]
       exact abs_lt.mpr ⟨by linarith only [hl],by linarith only [hx,mul_lt_mul_of_pos_right hx hf,hh]⟩
    obtain ⟨g,hg,hV,hU⟩:= ((show ∀ᶠ t:ℝ in 𝓝[>] 0, 0<t from self_mem_nhdsWithin).and ((show ∀ᶠ t:ℝ in 𝓝[>] 0,t<Y.a b/2 from mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (half_pos (Y.a_pos b)))).and (eventually_all.mpr fun i=> eventually_all.mpr fun j=>eventually_all.mpr fun a=> mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (sub_pos.mpr (he i j a)))))).exists
    have ht i j:atStop Y b (C i j) g (T i j) := fun a=> by specialize hU i j a; linarith
    refine ⟨s,g,hg,fun i=> ⟨C i,?_,ht i⟩⟩
    refine distinct_stops Y (Points.cons 0 (T i)) (gap_down (clear_rotates s _ _ (hs i)) hp) hg.le 0 _ (fun j=> Fin.cases ?_ (fun j=> ?_) j)
    · intro i; simp [atStop,Schedule.gridPoint,Points.cons,sub_pos.mpr hV]
    simpa only [Points.cons,Fin.cons_succ,points_apply,add_zero] using (ht i j)
lemma open_tile (g:ℝ): IsOpen {y:Seen n| noSeam Y b g y}:=by
    refine isOpen_iff_mem_nhds.mpr (fun x hx=>?_)
    change noSeam Y b g x at hx; choose c hc he using (fun i=> hx i)
    filter_upwards [eventually_all.mpr fun i=> eventually_all.mpr fun j=> (show ∀ᶠ y in 𝓝 x, atStop Y b (c i j) g (y i j) from (show Continuous (fun y:Seen n=> y i j) by fun_prop).continuousAt.eventually ((atStop_open ..).mem_nhds (he i j)))] with y hy
    exact fun i=>⟨_,hc i,hy i⟩
lemma pave (s:Ortho) : Continuous (revolve (n:=n) s):=by
    refine continuous_pi fun i=>?_
    change Continuous (fun y:Seen n => Points.move s (y i)); unfold Points.move points; simp_rw [← Ortho.motion_at]; fun_prop
end YM.Frontier6
