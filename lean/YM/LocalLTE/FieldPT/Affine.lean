import YM.LocalLTE.FieldPT.Rotate
/-! Cylinder payment at true detectors. Uses complete S.phase despite shared chart; handles Beacon mass via stencil weights not torus size. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Weft
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Mask Matter Coat Frond
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c L : Side}
open Fan Brush Foramen Pastel
variable {v z r C w s t y η γ B a ε α κ K: ℝ} {j n m k N M : ℕ}
open Weft AnalyticBridge AnalyticBridge.VerifiedReset FrameBox Tensor
local notation "E"=> Directions G c
namespace Scene
-- Radius pricing for forests composed with increments 1. Near points payment after all meters, no governor.H
lemma posted (G:Gauge) (L:Side)(hκ:Reliable G κ K){M:ℝ→ℕ}(hp: Rate G L 0 fun i=>(M i:ℝ))(j:ℕ) : ∃ B :ℝ→ℝ, Rate G L 0 B∧∀ t:ℝ,∀ (c:Side)(o:Site c)(X:Grove o) (i:ℕ), i≤ M t→ 1 ≤ B t∧ Brush j (B t) 1 ((X.crook i Chi.canonical κ) ∘ Grove.soloV (G:=G)) 0 := by
    obtain ⟨C,hC,H⟩:= Cabana.thick G j
    obtain ⟨J,D,hP⟩:=Frond.cleanly G j 1 zero_lt_one
    have he :0≤J:= (hP.sound (1:G.El) (by rw [G.mat_one,sub_self,norm_zero]; exact hP.pos.le)).nonneg
    let v t := (1+Blaze.royalty G)*Frame.expense G (M t) C
    let f t:=1+j.factorial*J*(1+v t)^j; have hx:Rate G L 0 v:=by
       let z t:= 4*(M t:ℝ)*(C*Blaze.royalty G); have he : Rate G L 0 z:= ((hp.mul_left _).mul_right _); unfold v Frame.expense; exact ((he.mul_right _).add ((Rate.const _).add he)).mul_left _
    refine ⟨f,(Rate.const 1).add ((((((Rate.const 1).add hx).pow j).weaken (by simp)).mul_left (j.factorial*J))),fun t c o X i hi=>?_⟩
    let s:ℝ:=8*i+1; let y:=G.colorScale
    let r:= min (κ/s) (D/(y*s))
    have hy:0 < y:= G.colorScale_pos; have hs:0<s:=by unfold s; positivity
    have hy':0 < r:=lt_min (div_pos hκ.down hs) (div_pos hP.pos (mul_pos hy hs))
    let u:=(Grove.soloV (G:=G) (c:=c)); have ha(β:Bond c):∀ᶠ x: Directions G c in 𝓝 0,G.chord (u x β) ≤ r:=by
         have he: G.chord (u 0 β)<r := by unfold u Grove.soloV; simp [hy']
         filter_upwards [(show Continuous (fun x=> G.chord (u x β)) from (by unfold u Grove.soloV; fun_prop)).continuousAt.eventually (gt_mem_nhds he)] with x hx using hx.le
    have hr:=FrameBox.climbs (G:=G) X hκ i (H c 0 (by simp)) hP (eventually_all.mpr ha) he hy'.le ((mul_comm s r).trans_le ((le_div_iff₀ hs).1 (min_le_left ..))) (show y*(s*r) ≤ D from (by rw [← mul_assoc, mul_comm]; exact (le_div_iff₀ (mul_pos hy hs)).1 (min_le_right ..)))
    have he' : 0≤ v t:=by unfold v Frame.expense; have hg:= royalty_ge G; have ht:= (H c 0 (by simp)).pos; positivity
    refine ⟨le_add_of_nonneg_right (by positivity),((hr.climb le_rfl (?_) : Brush j (j.factorial*J) (v t) _ _).trim.climb (le_add_of_nonneg_left zero_le_one) le_rfl)⟩; unfold v Frame.expense; have ht:= (H c 0 (by simp)).pos; have he:=royalty_ge G; gcongr
-- wedge stencil θ.
variable (hG:G.Simple) {p:BudgetPoint} (a':RegularAddress c)
def form (i:PlaqAxes): E:= fun e=> if e.1 ∈ a'.support then (wedge i (spike G)|>.field a'.site) e else 0
include hG
lemma trumpet (g:PlaqAxes) (h : a'.support ⊆ neighbors m a'.site): ‖form (G:=G) a' g‖ ≤ m:= by
    refine (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).mpr fun i=> ?_; unfold form; split
    next hf=> rw [wedge_field]; split
              next hv=>
                rw [norm_smul,spike_norm hG,mul_one]; apply le_trans (small_coord ..); exact Nat.cast_le.mpr (by rw [separation_comm]; exact ((neighbors_mem ..).1 (h hf)))
              rw [norm_zero]; positivity
    rw [norm_zero]; positivity
lemma agreesC {f:Config G c→ℝ} (hf:p.Regular a'.support f) (i j:PlaqAxes) : VerifiedReset.coeff f a'.site i j = logHessian f (form a' i) (form a' j):= by apply hessian_agrees hG hf _ _ <;> exact (fun i hi hp=> (if_pos hi).symm)
lemma implies (i j:PlaqAxes){K:ℕ}{g:ℝ→ Config G c→ℝ} (he:Arp K 2 C (fun s=>g s ∘ increment 1)) (hp:a'.support⊆neighbors m a'.site)(hh:∀ s∈clip,p.Regular a'.support (g s)) : Hex K (fun s=> projection a' (g s) i j) ∧ ∀ s∈clip,|s^2* projection a' (g s) i j| ≤ C*(m:ℝ)^2 :=by
    unfold projection; split
    next h=>
      let P (s:ℝ):= g s ∘ increment (1:Config G c); let V(s:ℝ):=iteratedFDeriv ℝ 2 (P s) 0; let X:= form (G:=G) a' i; let Y:=form (G:=G) a' j
      let A:Fin 2 → Directions G c:=![X,Y]
      have h s (hp:s∈clip): VerifiedReset.coeff (g s) a'.site i j=V s A:= agreesC hG a' (hh _ hp) i j
      refine ⟨Hex.change (f:=fun s=>V s A) ?_ (fun s hs=>(h _ hs).symm),fun s hs=> ?_⟩
      · have hx:Hex K V:=by
           let t:ℕ:= 2; refine ((he.coeffHex 2 le_rfl).oneZ (t.factorial:ℝ)).change fun s hs=>?_ ; change (_:ℝ) • ((t.factorial:ℝ)⁻¹ • _) = _; rw [smul_inv_smul₀]; positivity
        exact hx.alpha (ContinuousMultilinearMap.apply ℝ (fun _:Fin 2=>E) ℝ A|>.toLinearMap)
      rw [h _ hs]; let p:=s^2 • V s; have ht :‖p‖≤C:=by
         have hI:=he.smooth hs
         rw [show p= _ from (orbJ s hI).symm]; exact (Brush.offer.mp (he.brush s hs)).2 2 le_rfl
      change ‖p A‖ ≤ _; have hx:p= _:=rfl
      apply (ContinuousMultilinearMap.le_opNorm p A).trans; have he' : ∏ j:Fin 2,‖A j‖ ≤(m:ℝ)^2:= by
          refine (prod_le_prod (fun _ _=> norm_nonneg _) (s:=univ) (g:=fun _=>(m:ℝ)) (fun z hz=> ?_)).trans_eq (by simp); fin_cases z
          · exact (show ‖X‖≤ m from Scene.trumpet hG a' i hp)
          exact (show ‖Y‖≤ m from Scene.trumpet hG a' j hp)
      exact mul_le_mul ht he' (prod_nonneg (fun _ _=>norm_nonneg _)) he.nonneg
    refine ⟨Hex.constant _,fun s hs=> ?_⟩; rw [mul_zero,abs_zero]; exact mul_nonneg he.nonneg (by positivity)
end Scene
end YM.LocalLTE.Weft
