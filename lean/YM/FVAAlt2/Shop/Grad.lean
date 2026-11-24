import YM.FVAAlt2.Shop.Wave
/-!
# At the leading momentum test we can integrate *unconstrained* Taylor jets
 along links. Radius/closure is in the Read at the actual section, and gauge
 terms are killed here only by gauge-invariance of the leading slot kernel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Shop
open Lattice Function Finset Filter Topology Wilson Labels Source Source.Drops
open Planned.PrimaryIntegral295.Place
open PertExtension PertExtension.Orb PertExtension.Orb.SlotEvaluation PertExtension.LatticePT
open Comparison.Stencils.Corona (Crumb Primary Binds Tally demonstrates act_simple plated scape)
open MS MS.Koszul MS.Native MS.Landau MS.Landau.Detect MS.Plane MS.Theater
open MeasureTheory intervalIntegral InnerProductSpace
open Work.G03 (castPos castPos_step)
open scoped Interval Topology ContDiff
variable {G:Gauge}{d m:ℕ}{F:Labels.Frame G d}{H:Hol G}
local notation "C"=> Comparison.Stencils.Corona.act

/-- points on the (positive orientation) link. -/
def track (x: Edge Cover)(t:ℝ):E4:= castPos x.1 + t • basis x.2
@[fun_prop] lemma trackSmooth (x:Edge Cover): ContDiff ℝ ∞ (track x):= contDiff_const.add (contDiff_id.smul contDiff_const)
lemma track_int (x:Edge Cover){E:Type}[NormedAddCommGroup E]{f:E4→E}(h: Continuous f): IntervalIntegrable (f ∘ track x) volume 0 1:= (h.comp (trackSmooth x).continuous).intervalIntegrable _ _

def coverage (m:ℕ)(p:Feet G m)(x: Edge Cover):= ∫ s:ℝ in 0..1, Tensor.diagonal (p.val x.2) (track x s)
lemma cover_frame (x:Edge Cover) (p:Feet G m): IntervalIntegrable (Tensor.diagonal (p.val x.2) ∘ track x) volume 0 1:= track_int x (Tensor.diag_smooth (p.val x.2) ∞).continuous

def folder (G:Gauge)(k:ℕ)(x:Edge Cover) : Feet G k→ₗ[ℝ] G.Color where
 toFun p:= coverage k p x
 map_add' p q:=by exact integral_add (cover_frame x p) (cover_frame x q)
 map_smul' r p:=by exact integral_smul ..
abbrev useSlot (f:RG.Slot)(m:ℕ)(p:Feet G m):= C (Tally f) (coverage _ p)

def met (f:RG.Slot)(k:ℕ): Feet G k→ₗ[ℝ] G.Color:= C (Tally f) (folder G k)
lemma met_spec (f:RG.Slot)(p:Feet G m): met f m p=useSlot f m p:=by unfold met useSlot; rw [act_simple f.offset f.plaq,act_simple]; rfl

def curlLeg (u:Crumb G)(k:ℕ): RealP (Feet G k):= Complex.ofRealCLM.toLinearMap ∘ₗ ( ( EuclideanSpace.proj u.2 ).toLinearMap ∘ₗ ( met u.1 k ) )
def offLeg (u:Crumb G)(k:ℕ): Witness G k:= (curlLeg u (k+1)) ∘ₗ step_in G k

lemma access_cost(J:Jet G)(x: Edge Cover): access (trunk d J) x= ∑ j∈ Finset.range (d-1), coverage (j+1) (step_in G j (J j)) x :=by
 unfold access partConnection; simp_rw [one_smul, Source.Drops.truncate, Source.potential]; rw [intervalIntegral.integral_finsetSum]; rfl
 intro i _; exact cover_frame x (step_in G i _)
lemma met_now (f:RG.Slot)(J:Jet G): Source.Drops.glow (trunk d J) f= ∑ j∈Finset.range (d-1), useSlot f (j+1) (step_in G j (J j)):=by
 change C (f.offset,f.plaq) _=_; rw [act_simple]; unfold useSlot; simp_rw [access_cost, act_simple f.offset f.plaq, Finset.sum_sub_distrib,Finset.sum_add_distrib]
lemma met_proj(f:Crumb G)(p:Feet G m): curlLeg f m p = (↑(C (Tally f.1) (coverage m p) f.2):ℂ):= by
 change (↑((met f.1 m p:G.Color) f.2):ℂ) = _; rw [met_spec]
lemma print_vertex (u: Crumb G)(d:ℕ): PertExtension.Heat.Ray.print d (MvPolynomial.X u)=∑ i∈Finset.range (d-1), page i (offLeg u i):=by
 apply Labels.eval_ext; intro J; rw [map_sum,PertExtension.Heat.Ray.display_jet]; simp_rw [Theater.bookX, Next.Rank.Spindle.text, MvPolynomial.aeval_X]
 let p:= Source.Drops.glow (trunk d J) u.1; rw [met_now]; -- ∑
 simp_rw [show ∀ f:ℕ→G.Color, (∑ i∈Finset.range (d-1), f i) u.2= (∑ i∈Finset.range (d-1), f i u.2) from fun f=> map_sum (EuclideanSpace.proj (𝕜:=ℝ) (ι:=G.ColorIndex) u.2) f _,Complex.ofReal_sum, offLeg,LinearMap.comp_apply, met_proj]

/-- The missing gradient part, killed exactly on linear lattice curls. -/
lemma coverage_grad (p: Head G (m+1))(x:Edge Cover) : coverage m (gradS G m p) x = Tensor.diagonal (p.val ()) (castPos (x.1+step x.2))- Tensor.diagonal (p.val ()) (castPos x.1):=by
 let v:=Tensor.diagonal (p.val ())
 let w:=Analysis.D (basis x.2) v
 change coverage _ _ _= v _-v _
 have hv:Tensor.diagonal ((gradS G m p).val x.2)= w:= Theater.workL (basis x.2) p ()
 unfold coverage; rw [hv, show castPos (x.1+step x.2)= track x 1 from by rw [castPos_step,track,one_smul], show v (castPos x.1) = v (track x 0) from by simp [track] ]
 apply integral_eq_sub_of_hasDerivAt (f:=v ∘ track x); swap; exact hv ▸ cover_frame x (gradS G m p) -- apart
 intro s _
 apply ((Tensor.diag_smooth (p.val ()) ∞).differentiable (by simp) (track x s)).hasFDerivAt.comp_hasDerivAt (f':=basis x.2)
 unfold track; simpa only [one_smul,zero_add] using ((hasDerivAt_id' s).smul_const (basis x.2)).const_add (castPos x.1)
lemma met_off (p: Head G (m+1))(u:Crumb G): curlLeg u m (gradS G m p)=0:=by
 rw [met_proj, act_simple u.1.offset u.1.plaq]; simp_rw [coverage_grad]; rw [add_right_comm u.1.offset]; -- abel in coordinates
 abel_nf; simp
lemma been (p:Feet G m) (u:Crumb G): curlLeg u m (carve G m p)= curlLeg u m p:= Theater.homeR m (curlLeg u m) (by ext i; exact met_off i u) p
lemma curlLeg_zero (u:Crumb G) (p:Feet G 0): curlLeg u 0 p=0:=by rw [← been p u,show carve G 0 p=0 from (Submodule.mem_bot ℝ).mp (by rw [← Theater.weightT G]; exact house p),map_zero]
end YM.FVAAlt2.Shop
