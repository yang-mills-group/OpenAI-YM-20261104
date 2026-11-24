import YM.LocalTaylorR2.Kiln.Floret
/-!
 # Brush in FRAME'S argument for a true length ticket.
 Use SLOT estimates with cost through the LENGTH cutoff.No assumptions on Euclidean dimension of probe/field. No collapsed length/mask near-period averages. Just wrapped within Step stamp, analytic outside mask built independently of outcome, pay mask separately.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Kiln
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Axial Channel Canvas Work.G05
variable {G:Gauge}{c f L n : Side} {S:StepData c f}{P:Teller G}{T:Tube G S}{F:Forest S.ratio}
variable {d j k p:ℕ}{s:ℝ}{R:Rep G f}
variable {X X': Coat T F} {A : ℕ→ Atom G d}{i:Trans f}
open Itinerary
lemma latentCost (j : ℕ) {b:ℕ} (S:StepData c f)(A:ℕ→ Atom G d) (i:Trans f) (u:ZipP G c f) {v:ℝ} (hq : Mode (shaft S) u j v) (hf:(A i.2.2).length ≤ b):
    Brush j ((A i.2.2).magnitude * ((royalty G ^2)^d)*(1+(d:ℝ)*(2*b*(v*royalty G)))^j) 1 (latent A S i) u := by
  let t:=(A i.2.2); let h:=t.leg; let V (x:ZipP G c f) := pull i.1 0 (shaft S x)
  let g (x: ZipP G c f) := fun j:Fin d=> (t.leg j).atSite (V x) i.2.1; let H:ℝ:= royalty G; let v':= 2*(b:ℝ)*(v*H)
  have he:= hq.pos; have hM:=royalty_ge G; change 1≤H at hM; have hv:0≤v':=by unfold v'; positivity
  have hh (c:Fin d)(q:G.ColorIndex): Brush j (H^2) v' (fun x=> g x c q) u:=by
    refine ((colorEvaluated q (slot_cost (t.leg c) i.2.1 he (Blaze.turn hq i.1).atLink)).climb le_rfl ?_)
    apply mul_le_mul_of_nonneg_right _ (by change 0 ≤ v*H; positivity)
    have hx : (t.leg c).length≤b:= (Finset.single_le_sum (f:=fun c=> (t.leg c).length) (fun i _=> Nat.zero_le _) (mem_univ _)).trans hf
    exact_mod_cast Nat.mul_le_mul_left 2 hx
  let z (c : Fin d → G.ColorIndex) (x : ZipP G _ _) := t.coeff c * ∏ i, g x i (c i)
  have hz (c : Fin d → G.ColorIndex): Brush j (‖t.coeff c‖*((H^2)^d)) (d * v') (z c) u:= by
    have hi:= (Brush.all_prod univ (fun i x=> g x i (c i)) _ _ (fun j _=> hh j (c j))).smul (t.coeff c); rw [sum_const, prod_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hi; exact hi
  exact ((Brush.spree univ z _ (mul_nonneg (Nat.cast_nonneg d) hv) (fun j _=> hz j)).climb (v:=t.magnitude*((H^2)^d)) (by simp only [Real.norm_eq_abs,Atom.magnitude,sum_mul]; rfl) le_rfl).trim

-- For all valid Step. Supply one beam width & magnitude price after true cutoff, for all d.
lemma latentRate (G:Gauge)(P:Teller G)(L:Side)(D:Patch)(hD:D.Branches P.bind G) (d j:ℕ):
    ∃ r B, 0 < r ∧ r ≤ 1 ∧ Rate G L 0 B ∧ ∀ x (c f:Side)(S:StepData c f)(T:Tube G S)(u:ZipP G c f)(A:ℕ→ Atom G d) (i:Trans f),
     S.patch=D→ P.Funds S T → ‖u‖ ≤ r → ∀ (_K : S.Choices), (A i.2.2).length ≤ till x → Brush j ((A i.2.2).magnitude * B x) 1 (latent A S i) u := by
  obtain ⟨r,v,hp,hr,hv,h⟩:=dressed P D hD j
  let g x:= 1+(d:ℝ)*(2*(till x:ℝ)*(v*royalty G))
  let B x := ((royalty G)^2)^d*g x ^j
  have hh : Rate G L 0 (fun x:ℝ=> (till x:ℝ)) := by
    apply Rate.radius_price.compare; apply Eventually.of_forall; intro i; rw [abs_of_nonneg (Nat.cast_nonneg (till i)),abs_of_nonneg (Nat.cast_nonneg (radiusB i))]; exact_mod_cast Nat.div_le_self _ _
  refine ⟨r,B,hp,hr,?_, fun x c f S T u A i hS hP hA k ht=> ?_⟩
  · have hg:Rate G L 0 g:= (Rate.const (1:ℝ)).add (((hh.mul_left 2).mul_right _).mul_left _)
    simpa only [zero_mul] using (hg.pow j).mul_left (((royalty G)^2)^d)
  have h:= latentCost j S A i u (h c f S T hP hS u hA k).2.1 ht
  exact h.climb (by unfold B g; ring_nf; rfl) le_rfl
end YM.LocalTaylorR2.Kiln
