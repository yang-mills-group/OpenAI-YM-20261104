import YM.TraceExtension.Verse.Round
import YM.OPE.Coverage.Freight
/-!
# From corrected two-mark replication to a budget for *one-field* slabs

Real estimates at the position-frame stations along a Trace construction.
Subslab of thickness of order the width of the *yard*, NOT the measuring length; a nontrivial
loss. We'll use these estimates on the very same fields for analytic continuation (no positivity
for Euclidean contact-extended correlators is implied).

The pair purchase matters here — it includes **all** marked subsets. Use the singleton and pay
for the one-point correction. No new transfer hypothesis; in particular no assumption about
master columns having low prices in fixed fields. This supports the moving labels on the
ordered filter, with the actual denominator, many copies and packed stencil geometry of that
purchase. No change to its E/K budgets. See TraceExtension/Prom/{...} for the hard receipt.

Proofs adapted from `TraceExtension/Verse/{Pears,Cape}` and
`TraceExtension/Prom/Orion/{Shine,Latch}` (this is in contrast on any `Gondola`, not under
`PoisedSky` for a separate rank/fixed outward window).
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Stamps
open Function Filter Set Extraction Table Cells OS OS.Ground Lattice Spec MeasureTheory Wilson Trace
open RG Trace.Terrace MergeProof.East Next.Rank Next.Rank.East Next.UVStress Further.CorrectedLift Climb Trace.Verse
open Glyph Next.Rank.Station Next.Rank.Tapes.West Analysis Marker Edition
open scoped Topology BigOperators InnerProductSpace Classical ContDiff
variable {G: Gauge} {C: Family G}{𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book} {d n i: ℕ}
variable {H:(Cells.standard C).Hierarchy}{J:Scaling S}{W:∀ i,Vane C i}{Y:∀ d _:ℕ,(Cells.standard C).Field d→L[ℂ] C.label d}
local notation "S'"=> Cells.standard C
local notation "A'"=> C.path.levels
local notation "U'"=> (𝓛:Filter (ℕ×ℕ))

private def every (s:ℝ): E4:= WithLp.toLp 2 (fun _=> s/2)
private def shot (s:ℝ):Points 2:= points ![0,every s]
private lemma shot_width {s:ℝ}(h:0 ≤ s):‖every s‖=s:=by
    apply (sq_eq_sq₀ (norm_nonneg _) h).mp
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_four]; unfold every;simp;ring
private lemma shot_generic {s:ℝ}(h:0<s): shot s∈generic 2:=by
    intro a i j hi; fin_cases i<;>fin_cases j <;>simp_all [shot,every,h.ne'];linarith
private lemma open_shot {s:ℝ}(hp:1/2 < s)(h:s < 2):Scaling.window 100 2∈𝓝 (shot s):=by
    let f(x:Points 2):=cubedist (x 0) (x 1)
    have hc: Continuous f:=continuous_cubedist.comp (show Continuous (fun x:Points 2=> (x 0,x 1)) by fun_prop)
    have hp':0 < s:=by linarith
    have hz: (100:ℝ)⁻¹ < f (shot s):=by
       simp only [f,shot,points_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,cubedist]
       apply lt_of_lt_of_le _ (dist_le_pi_dist _ _ timeAxis); change _ < dist (0:ℝ) (s/2); rw [Real.dist_eq, zero_sub,abs_neg,abs_of_pos (by linarith)]; linarith
    have hu: ‖shot s‖ < 100:=by
       have ht:= PiLp.norm_sq_eq_of_L2 _ (shot s); have hw:= shot_width hp'.le
       change ‖points ![(0:E4),every s]‖ < (100:ℝ); simp only [Fin.sum_univ_two,shot,points_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,norm_zero, pow_two,zero_mul,zero_add,hw] at ht; nlinarith
    apply mem_of_superset ((IsOpen.inter (isOpen_lt continuous_const hc) (isOpen_lt continuous_norm continuous_const)).mem_nhds (show (shot s) ∈ {x| (100:ℝ)⁻¹ < f x} ∩ {x:Points 2 | ‖x‖ < 100} from ⟨hz,hu⟩))
    intro x hx; refine ⟨?_, (show ‖x‖ < _ from hx.2).le⟩
    intro i j hij; have hg:(100:ℝ)⁻¹ ≤ f x:= (show (100:ℝ)⁻¹ < _ from hx.1).le
    fin_cases i<;>fin_cases j <;> first| (exfalso; exact hij (by decide)) | exact hg| exact hg.trans_eq (dist_comm ..)


lemma purchase_scene (hG:G.Simple)(h : Gondola f H J 𝓛 W Y):
    ∀ᶠ i:ℕ in atTop, ∃ x:Points 2, x 0=0 ∧
      FitSky (A') (W i|>.b) (W i|>.k) x ∧ fad (W i) x ∈ Scaling.window 100 2 := by
  have hx := rounds h hG (shot 1)
  filter_upwards [hx.eventually (open_shot (s:=1) (by norm_num) one_lt_two),
    hx.eventually ((genericOpen 2).mem_nhds (shot_generic (s:=1) zero_lt_one))] with i hi hi'
  exact ⟨_, rfl, Trace.Verse.mixed h _ i hi' hi.2, hi⟩

-- Canonical heightV name at this station
abbrev held (i d : ℕ) (z : ℕ × ℕ) (v : (Cells.standard C).Field d) : C.book.Token :=
    ⟨d,heightV W i d z v⟩

def purchaseWidth (V: Vane C i) := widthSky (A') V.b V.k

-- at the origin of the stencil. Subtraction in the singleton component of the actual pair.
set_option maxHeartbeats 1500000 in
lemma pair_origin (hL: 𝓛.toFilter ≤ f.fuse) (h: Gondola f H J 𝓛 W Y) (hC : C.Makes)
    (s:ℝ) (hs:1/2 < s)(hs':s<2) (hG:G.Simple) (t:PegC C d):
    ∃ A:ℝ, 0 ≤ A ∧ ∀ᶠ i in atTop, ∀ᶠ u:ℕ×ℕ in U',
    centeredBudget C (held (W:=W) i d u (PoleC C d t)) A (purchaseWidth (W i)) u.1 u.2 := by
  let T:Fin 2→ (S').Field d := fun _=> PoleC C d t
  let I : Fin 2 → (S').Tag := fun j=>⟨d,T j⟩
  let m : Points 2→ veil (Fin 2) := fun x=>Read.maxProfile C x I
  let b:ℕ→ℂ:=fun i=>(m (fad (W i) (shot s))).part (slot 0)
  let P:ℝ := ‖(m (shot s)).part (slot 0)‖ + 1
  have hp : 0 < P:=by unfold P; positivity
  have hx := rounds h hG (shot s)
  have hsG := shot_generic (s:=s) (by linarith)
  have hP : Tendsto (fun i=> ‖b i‖) atTop (𝓝 (‖(m (shot s)).part (slot 0)‖)) :=
    (((Read.profile_part_cont (S') H.smooth I (slot 0)).norm).continuousAt
        ((conf_open 2).mem_nhds (generic_conf _ hsG))).tendsto.comp hx
  refine ⟨1+P, by positivity,?_⟩
  filter_upwards [hx.eventually (open_shot hs hs'),
    hx.eventually ((genericOpen 2).mem_nhds hsG), eventually_ge_atTop d,
    hP.eventually (ge_mem_nhds (show _ < P by unfold P; linarith)),
    cost_clears.eventually (ge_mem_nhds zero_lt_one)] with i hi hi' hd hb hE
  let V := W i; let x:=shot s; let k:=V.k; let w:=purchaseWidth V; let q:=fad V x
  let j: Fin (i+1):=⟨d,Nat.lt_succ_of_le hd⟩
  have ht:=Trace.Verse.mixed h x i hi' hi.2
  let v: ℕ→ℕ→Fin 2→C.label d:= fun N p c=> V.wheel.atCut (N,p) j (T c)
  have hI': ∀ᶠ u:ℕ×ℕ in f.fuse, ∀ h : w ≤ u.1, ∀ o:Site (C.side u.1 u.2), ∀ v:C.label d,
      Interior ((Cells.center C.S u.2 h o).chamber 0) (C.O u.1 u.2 v o) := by
    rw [Extraction.Order.fused]; unfold Extraction.Order.late
    exact Eventually.of_forall fun _ => (f.mesh.cofinal.eventually (Stock.clear_interior C hC w d)).mono
      fun _ h _ => h.choose_spec _
  filter_upwards [(link_mesh hL).eventually (ht.stencils hC d),
      (link_mesh hL).eventually_gt_atTop (max k (C.ref d)), hI'.filter_mono hL] with u hu hk hU
  obtain ⟨hn, hu⟩ := hu
  let N:=u.1; let p:=u.2
  change max k (C.ref d) < u.1 at hk
  have hk' : k < N := lt_of_le_of_lt (le_max_left ..) hk
  have hw:w ≤ N := (widerSky ..).trans ((beforeSky ..).trans hk'.le)
  let L:= Ship.yardSky C V.b hk'.le p; let β:=C.beta N p
  let a := C.O N p (v N p 0) 0
  let tagY := q_asked (C:=C) (d:=fun _ : Fin 2=>d) (v N p)
  let c := Ship.clients C tagY V.b V.k N p x
  let P' : (Config G (C.side N p) → ℂ) := fun U=>
    (Read.cylinder (Read.cumulants C q I (Ship.fittingSky ht)) c U).part (slot 0)
  have hC'(U : Config G (C.side N p)):
      Ship.invoiceSky (Next.Rank.Atlas.jointX (d0:=fun _ : Fin 2=>d) (fun j=> Further.CorrectedLift.ladder C d (T j))) tagY ht N p U
        = Read.cylinder (Read.cumulants C q I (Ship.fittingSky ht)) c U := by
    have hz: Next.Rank.Atlas.jointX (d0:=fun _ : Fin 2=>d) (fun c=> Further.CorrectedLift.ladder C d (T c)) = I := by
      funext i; simp only [I,Atlas.jointX]; rw [ladder_reads]
    rw [hz]; rfl
  have hX : L.rootTest β P' ≤ costHint i := by
    unfold P'; simp_rw [← hC']
    exact (h.season i).1.plate.boot j (fun _=>t) N p hk' x hi ht (slot 0) (show ({0}:Finset (Fin 2)).Nonempty from Finset.singleton_nonempty _)
  have hzero : (Next.Rank.Station.choose (A') V.b V.k x) 0=0:=by
    ext; simp [Next.Rank.Station.choose,address,x,shot]
  have ha : c 0=a:=by unfold c Ship.clients Read.probes; rw[hzero]; change C.O _ _ _ (Cells.location C.S k _ _ 0)=_; rw [location_origin]; rfl
  have hπ:P'=a-b i • (1 : Config G (C.side N p) → ℂ):=by
    funext U; unfold P'; rw [Read.cylinder_single (Read.cumulative ..),ha]; change _=a U-b i * 1; rw [mul_one]
  have hv: Interior (L.chamber 0) a:= hU hw 0 _
  have hx':Interior (L.chamber 0) P' := Read.raw_in L c (fun i=> hu _ _ _) _ (slot 0)
  rw [held,heightV,dif_pos hd]
  refine ⟨hw,(le_max_right ..).trans hk.le,fun o=> ⟨hU _ _ _,?_⟩⟩
  change (center C.S p hw o).rootTest β (C.O N p (v N p 0) o)≤1+P
  rw [show (center C.S p hw o).rootTest β _= L.rootTest β a from Stock.translate_s hw o ⟨d,v N p 0⟩ hv,show a=P'+ b i • 1 by rw [hπ,sub_add_cancel]]
  refine ((seamless hC N p).semi L _ _ hx'
    ((show Interior (L.chamber 0) (1:Config G _ → ℂ) from Interior.constant _ (1:ℂ)).scale (b i))).trans ?_
  change L.rootTest β P' + L.rootTest β (b i • (1:Config G (C.side N p)→ℂ)) ≤ _
  rw [Next.Extract.root_smul,Tiling.root_one,mul_one]; exact add_le_add (hX.trans hE) hb

end YM.GapsContact.Stamps
