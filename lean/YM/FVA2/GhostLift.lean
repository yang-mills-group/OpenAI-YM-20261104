import YM.FVA2.OrthPlane

/-!
# Real-chart check for the ghost interaction and Haar

On Landau's plane constant ghosts do not couple. The rest *do*,
including at fixed sites. This proof does not use formal cohomology
on the harmonic global modes (would not work).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Inversion
open Function Set Finset Filter Lattice MS MS.Koszul MS.Swirl MS.Native MS.Orbit MS.Orbit.Cog
open MS.Bare Gauge
open PertExtension PertExtension.Orb
open Matrix Ends ArrayMap Substitute Lag
open scoped Classical Topology RealInnerProductSpace ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n:Side}
local notation "T"=> transP (G:=G) (n:=n)
local notation "L"=> plane (G:=G) (n:=n)
local notation "I"=> incl G n
local notation "D"=> pin G n
local notation "F"=> tallyY (G:=G) (n:=n)

abbrev enterF (G:Gauge)(n:Side) : RootX G n→L[ℝ] FullX G n:= (incl G n).toContinuousLinearMap
local notation "C"=> enterF G n
lemma path_tan (t:RootY G n) (h:Even n.val) : ∀ᶠ a : RootX G n in 𝓝 0,
      (full n).flow (I a) (D t)=I ((root n).flow a t):= by
   obtain ⟨s,hs,H⟩:=LocalH.geom_patch G
   have he : ∀ e:Edge (Site n), Tendsto (fun u:RootX G n=> I u e) (𝓝 0) (𝓝 0):= by
      intro i; have hh:= ((continuous_apply i).comp (C).continuous).tendsto (0:RootX G n); simp at hh; exact hh
   filter_upwards [ eventually_all.mpr (fun i=> (he i).eventually (Metric.ball_mem_nhds (0:G.Color) hs)) ] with a ha
   have hv(e:OEdge n) : (full n).flow (I a) (D t) e.val=I ((root n).flow a t) e.val := by
      rw [lifted]; change Maurer.volts _ (I a _) =_; rw [lifted]; rfl
   have hx(e:Edge (Site n)) : (full n).flow (I a) (D t) (Orb.reflect e)= - ((full n).flow (I a) (D t) e) := by
      change Maurer.volts ((full n).morph (Orb.reflect e) _) (I a (Orb.reflect e)) = -Maurer.volts ((full n).morph e _) (I a e)
      rw [refl_lift h,show (full n).morph (Orb.reflect e) (D t)= ((full n).morph e (D t)).swap from ?_]; exact Maurer.comeback_field _ (H _ (le_refl s)) (ha e)
      change (D t (-e.1-step e.2), D t (-e.1-step e.2+step e.2))=(D t (e.1+step e.2),D t e.1)
      rw [sub_add_cancel,show -e.1-step e.2= -(e.1+step e.2) from (by abel),pin_even,pin_even]
   funext x; rcases eR_spec x with hl|hl
   · exact hv ⟨x,hl⟩
   apply neg_inj.mp; rw [← hx, ← refl_lift h]; exact hv ⟨Orb.reflect x,by rw [eR_reflect,hl]⟩
lemma pureY (v:G.Color) (b:RootX G n) (h:Even n.val): ∀ᶠ a:RootX G n in 𝓝 0,
      chartPair (I (L b)) ((full n).flow (I (T a)) (fun _=>v))=0:= by
    obtain ⟨s,hs,H⟩:=LocalH.geom_patch G
    have he(z:Edge (Site n)): Tendsto (fun u:RootX G n=> (I (T u) z)) (𝓝 0) (𝓝 0):= by
       let f:= C ∘L T; have ht:=((continuous_apply z).comp f.continuous).tendsto (0:RootX G n); simp at ht; exact ht
    filter_upwards [eventually_all.mpr (fun z=>(he z).eventually (Metric.ball_mem_nhds _ hs))] with a ha
    let P:=I (T a); let q (x:ℝ): G.El:=G.lieExp (-(x • v)); let R (x:ℝ): FullX G n:=fun w=> G.adjoint (q x) (P w); let W:FullX G n:= (full n).flow P (fun _=>v)
    have hp(i:Edge (Site n)): HasDerivAt (fun x:ℝ=> R x i) (W i) 0:= by
       have hh:= Maurer.amp (v,v) (H s (le_refl _)) (ha i); convert hh using 1; swap; · rfl
       funext x;
       have hx: Maurer.step (v,v) (P i) x= G.lieExp (G.adjoint (q x) (P i)):= by rw [Maurer.runby]; unfold Maurer.step q; simp only [ Next.SectorChange.exp_negative,inv_inv]
       apply Eq.symm; change G.plog (G.mat (Maurer.step (v,v) (P i) x))=_; rw [hx];
       apply Maurer.snap_on (H s (le_refl _)); simpa [Metric.mem_ball] using ha i
    have hx:HasDerivAt R W 0:= hasDerivAt_pi.mpr hp
    have hh: HasDerivAt (fun t:ℝ=> chartPair (I (L b)) (R t)) (chartPair (I (L b)) W) 0:=
       HasDerivAt.fun_sum (fun i _=> ((projector i).hasFDerivAt.comp_hasDerivAt (𝕜:=ℝ) 0 hx).const_mul _)
    rw [show (fun t:ℝ=> chartPair (I (L b)) (R t))=fun _=>0 from ?_] at hh
    · exact hh.unique (hasDerivAt_const ..)
    funext k; unfold R P; rw [plane_read (T a) (q k),base_pair _ _ h, adj_pair h, mul_zero]

lemma path_plane (t:RootY G n) (b:RootX G n) (h:Even n.val): ∀ᶠ a:RootX G n in 𝓝 0,
    chartPair (I (L b)) ((full n).flow (I (T a)) (F t)) =
       2 * chartPair (L b) ((root n).flow (T a) t):= by
    have he : F t = D t-(fun _=> meanY (D t) 0):=rfl
    have hu: Tendsto T (𝓝 0) (𝓝 0):= by simpa using (T).continuous.tendsto (0:RootX G n)
    filter_upwards [ pureY (meanY (D t) 0) b h, hu.eventually (path_tan t h) ] with a ha hh
    rw [he,map_sub, show ∀ v w : FullX G n, chartPair (I (L b)) (v-w)=chartPair (I (L b)) v-chartPair (I (L b)) w from fun p v=>by simp only [chartPair,map_sub,mul_sub,Finset.sum_sub_distrib],ha, sub_zero, hh, base_pair _ _ h]
lemma even_haar (h:Even n.val): ∀ᶠ a:RootX G n in 𝓝 0,
    (2:ℝ)⁻¹*measure_term (I a)=measure_term a:= by
    filter_upwards [eventually_all.mpr (fun i:OEdge n=>((continuous_apply (A:=fun _:OEdge n=>G.Color) i).tendsto (0:RootX G n)).eventually (Maurer.opposite))] with a ha
    change _* ∑ i:Edge (Site n), Maurer.lac (I a i)= ∑ i:OEdge n,Maurer.lac (a i); rw [sum_edges _ h]; simp_rw [lifted, refl_lift h, lifted,ha, Finset.sum_add_distrib]; ring

end YM.FVA2.Inversion
