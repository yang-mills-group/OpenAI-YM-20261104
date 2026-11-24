import YM.MS.Graphical.InteriorJet

/-!
# Move from a common pole-height bound with a section that works for every scale

Suppose an assembled group is regular at z=0 (after collecting all its CT
graphs). Suppose we initially have estimates only with poles cleared
(multiplying by some power of z). Transfer the estimates to the group
itself at a smaller radius, still uniformly in log length, retaining `PinPrice`
forall-power estimates if present. The proof divides the analytic family by z
successively, with interior pricing.
-/

noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric Complex
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open scoped Topology ContDiff Interval
variable {b c : Bool} {R a p : ℝ} {G : Gauge} {F H : Schedule G} {z : ℂ} {k m n : ℕ} {q r : ℤ}

lemma from_except (hf : ∀ t, Hol (disc R) (F t)) (hr : 0<R) (hv : ∀ z∈disc R, z ≠ 0→ BorelRow fun t=>F t z)
    (ht : ∀ z∈disc R, z ≠ 0→∀ t, Issue q (F t z) ∧ Sturdy false (F t z)) : AtPin R q F:= by
  have h0 t:= Wind.cake (hf t) hr
  have H (z :ℂ) (hz : z∈disc R) (t) : Issue q (F t z) ∧ Sturdy false (F t z):= by
    by_cases h:z=0; swap; · exact ht z hz h t
    subst z; refine ⟨Wind.peerU (h0 t) ?_, Wind.time (h0 t) ?_⟩
    · filter_upwards [dotty_bill hr,dotty_non] with i hi hm; exact (ht i hi hm t).1
    filter_upwards [dotty_bill hr,dotty_non] with i hi hm; exact (ht i hi hm t).2
  refine ⟨ hf, fun z hz=>?_,fun t z hz=>(H z hz t).1, fun t z hz=>⟨(hf t).link hz isOpen_ball,(H z hz t).2⟩ ⟩
  by_cases h:z=0; swap; · exact hv z hz h
  classical
  subst z; intro m w; let f z t := if h:z∈disc R ∧ z ≠ 0 then F t z m w else 0
  refine measurable_of_tendsto_metrizable' (f:=f) dotty ?_ (tendsto_pi_nhds.mpr fun i=>?_)
  · intro i; by_cases hi:i∈disc R ∧ i≠0; swap; · simp only [f,dif_neg hi]; exact measurable_const
    simp only [f,dif_pos hi]; exact hv i hi.1 hi.2 m w
  refine (h0 i m w).congr' ?_; filter_upwards [dotty_bill hr,dotty_non] with j hj hp; unfold f; rw [dif_pos (show j∈disc R ∧ j≠0 from ⟨hj,hp⟩)]

lemma scaleDown_credit (hf : PinPrice b R q F) (hp : 0<R) (h : ∀ t, F t 0=0) :
    PinPrice b (R/2) q (scaleDown F) := by
  obtain ⟨A,H⟩:= hf; have hr : R/2≤R:= by linarith
  have he (z : ℂ) (hz : z≠0) (t:ℝ) : scaleDown F t z=z⁻¹ • F t z:= by unfold scaleDown; rw [hung hz,h,sub_zero]
  refine ⟨(from_except (F:=scaleDown F) (q:=q) (fun t=>HolG (A.analytic t) hp) hp ?_ ?_).resize hr le_rfl,?_⟩
  · intro z hz hv m w; simp_rw [he _ hv]; exact ((A.borel z hz m w).const_mul z⁻¹)
  · intro z hz hv t; rw [he _ hv]; exact ⟨fun i=>Limit.smul z⁻¹ (A.capacity _ _ hz i), Sturdy_scale (A.fine t _ hz).token _⟩
  cases b with
  | false=> obtain ⟨a,ha⟩:= show Subponential R F from H; exact show Subponential _ _ from ⟨a, inherit_pay ha h A.analytic hp⟩
  | true=>exact show InPins _ _ from fun a=> inherit_pay ((show InPins R F from H) a) h A.analytic hp

-- currency for such sections
namespace Countered
lemma repriced (hf : Countered b q F) (he : TimeEq F H) : Countered b q H:= by
  obtain ⟨R,F',hR,hF,h⟩:=hf; exact ⟨R,F',hR,he.symm.trans' hF,h⟩
lemma up (h : Countered b q F) (ht : q≤r) : Countered b r F:= by
  obtain ⟨R,X,hR,hX,h⟩:=h; exact ⟨R,X,hR,hX,PinPrice.resize h le_rfl ht⟩
lemma zero' (b : Bool) (G : Gauge) (q : ℤ) : Countered b q (0:Schedule G) := by
  obtain ⟨R,hR,H,V⟩:= shortening zero_lt_one zero_lt_one; exact ⟨R,0,hR,TimeEq.refl _,PinPrice.zero' ..⟩
lemma static2 (h : Countered b q F) (hp : Countered c r H) :
    ∃ (R:ℝ) (X Y:Schedule G), Short R ∧ TimeEq F X ∧ TimeEq H Y ∧ PinPrice b R q X ∧ PinPrice c R r Y:= by
  obtain ⟨R,X,hR,hX,h⟩:=h; obtain ⟨T,Y,hT,hY,hp⟩:=hp; obtain ⟨Z,hZ,hF,hH⟩:=shortening hR.1 hT.1; exact
     ⟨Z,X,Y,hZ,hX,hY,PinPrice.resize h hF le_rfl,PinPrice.resize hp hH le_rfl⟩
lemma add (h : Countered b q F) (hp : Countered b q H) : Countered b q (F+H):= by
  obtain ⟨R,X,Y,hR,hX,hY,h,hp⟩:=static2 h hp; exact ⟨R,X+Y,hR,hX.add hY,PinPrice.add h hp⟩

lemma unloads (hf : Countered b q (fun t=>paid n (F t))) (hv : ∀ t, Live (F t)) :
    Countered b q F := by
  induction n with
  | zero=> simpa only [pay_zero] using hf
  | succ n ih=>
     obtain ⟨R,X,hR,H,hX⟩:= hf; have he:0<R:=hR.1
     have ht (t:ℝ): X t 0=0 := Lift.unique (hX.1.Lift H he t) (dry (hv t) 0 (by omega))
     apply ih; refine ⟨_,_,hR.less (half_pos he) (by linarith only [he]), ?_, scaleDown_credit hX he ht⟩;
     apply (H.and dotty_non).mono; intro i hi t; obtain hp:= hi.1 t; dsimp only at hp; dsimp only [scaleDown]; rw [hung hi.2, ht,sub_zero, ← hp,paid_s]; dsimp only; rw [inv_smul_smul₀ hi.2]
end Countered
end YM.MS.Graphical
