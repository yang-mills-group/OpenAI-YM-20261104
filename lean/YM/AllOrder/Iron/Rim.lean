import YM.AllOrder.Iron.Root
import YM.Next.STATIONARY.OneLoop.Lattice
import YM.Next.STATIONARY.Loops.Fourier
import YM.AllOrder.Iron.Poise
import YM.Next.STATIONARY.Block.Static
import YM.TraceExtension.Perfect.Stove
import YM.Next.STATIONARY.Joint.FourPoint
import YM.Next.STATIONARY.Joint.HaarJac
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Iron
open Lattice Laurent RG Filter Tree Metric Finset Function Gauge Matrix Module
open Exterior Wilson Precision Tree MeasureTheory Stationary
open scoped Matrix BigOperators Topology Classical ContDiff InnerProductSpace Matrix.Norms.Frobenius ENNReal
variable {G:Gauge}{c f:Side}{S:StepData c f} (F:Forest S.ratio)(t:S.Choices) {p:Clip}{R:PathData G}

variable (i: G.ColorIndex)
open Wilson Precision
-- price envelope. row norm via resulting decay
open Bloch Laurent Audience
open scoped ComplexConjugate
variable {α : Type}[Fintype α][DecidableEq α] {σ A:ℝ}{v:Momentum}
-- Fourier node vs finite complex Fourier reconstruction.
def foil (A:Momentum→ CompM α α)(n:Side): CircM n α α := Matrix.of fun x y=> ∑' p:Cover, if x.1+wrap n p = y.1 then Laurent.market (fun p=>A p x.2 y.2) 0 p else 0
variable {Q : Momentum→CompM α α} {n m:Side}
lemma foil_germ (h:∀ i j,Firm σ A (fun p=>Q p i j)) : Jaunt (foil Q n) Q 0 := by
    let F (i j:α):= Laurent.market (fun p=>Q p i j) 0; have hG i j : Width (σ/4) (royalty σ A) (F i j):=by have hs:= (h i j).width_pos; exact (h i j).1.issues (h i j).2 (σ/4) (σ/4) (by positivity) (by positivity) (by linarith)
    refine Jaunt.atmosphere ?_ -- import?
    intro p q hQ b t i
    let T:= Q q
    have he : foil Q n *ᵥ relay p b=tune p (T*ᵥ Pi.single b 1):=by
       ext z; let i0:=z.1; let l:=z.2; let g:=F l b; let y v:= i0+wrap n v; have hx:=h l b; have hs:= (hG l b).summable (show 0≤σ/4 from by linarith only [hx.width_pos]);
       let D(v:Cover)(u:Site n):= if y v=u then g v else 0; have ht (u:Site n):Summable fun v=> D v u := (hs.indicator (s:={v| y v=u})).congr fun x=> Set.indicator_apply ..
       rw [Matrix.mulVec, dotProduct,Fintype.sum_prod_type]; unfold relay tune; simp only [Pi.single_apply, mul_ite, Finset.sum_ite_eq', Finset.mem_univ,mul_zero, ↓reduceIte,mul_one] -- check
       -- reduce before tsum
       obtain ⟨x,hxP⟩:=hQ
       have hh : Q q l b=Q (mon p) l b:=hxP.symm ▸ hx.1.reset (mon p) (hx.in_range (real_frequency p)) x
       rw [mulVec_single_one]; change ∑ w,(∑' v,D v w)*cell p w=cell p i0 * Q q l b; simp_rw [← tsum_mul_right]; rw [← Summable.tsum_finsetSum (fun i _=> (ht i).mul_right (cell p i))]
       rw [hh,← show _ = Q (mon p) l b from hx.1.paints hx.2 _ (hx.in_range (real_frequency p)), Laurent.read,←tsum_mul_left]; apply tsum_congr; intro z; rw [Finset.sum_eq_single_of_mem (y z) (Finset.mem_univ _) (by intro i _ he;simp [D,Ne.symm he])]; simp only [D,↓reduceIte, y, cell_add,cell_wrap,smul_eq_mul]; unfold g F; ring
    rw [he]; unfold relay; rw [ray_dots]; split
    next ht=> simp [ht,T]
    simp_all
omit [Fintype α] [DecidableEq α] in
lemma foil_fee {i j:Co n α} (h:∀ i j,Firm σ A (fun p=>Q p i j)) : ‖foil Q n i j‖ ≤ royalty σ A * Push.Uniform.Decay (σ/4) i.1 j.1 := by
   let a:=σ/4; have hp := (h i.2 j.2).width_pos; have hx:0<a:=by unfold a; positivity
   let F:= Laurent.market (fun p=>Q p i.2 j.2) 0; have he:= (h i.2 j.2); have hA: Width a (royalty σ A) F:= he.1.issues he.2 a (σ/4) hx.le hx (by unfold a; linarith);
   let D:= Push.Uniform.Decay a i.1 j.1; have hd:= Push.Uniform.decay_pos a i.1 j.1; let g (v:Cover):= if i.1+wrap n v=j.1 then F v else 0; let G v:=Real.exp (a*size v)*‖F v‖; change ‖∑' v,g v‖ ≤ _ * D
   have hh(v) : ‖g v‖ ≤ G v * D:=by
       unfold g; split
       next hv =>
          have ht : separation i.1 j.1≤ size v:= by rw [←hv,add_comm i.1,separation_comm,separation,add_sub_cancel_right]; exact Next.Free.within_size _ _ -- name
          have ht' : (separation i.1 j.1:ℝ)≤size v:=by exact_mod_cast ht
          refine (le_mul_of_one_le_right (norm_nonneg _) (show 1≤ Real.exp (a*size v)*D from ?_)).trans_eq ?_
          · unfold D Push.Uniform.Decay; rw [← Real.exp_add]; apply Real.one_le_exp; nlinarith [ht']
          unfold G; ring
       rw [norm_zero]; exact mul_nonneg (hA.1 _) hd.le
   have hv:= Summable.of_nonneg_of_le (fun v=> norm_nonneg _) hh (hA.2.1.mul_right D); refine (norm_tsum_le_tsum_norm hv).trans ((hv.tsum_le_tsum hh (hA.2.1.mul_right D)).trans ?_); rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hA.2.2 hd.le
end YM.AllOrder.Iron
