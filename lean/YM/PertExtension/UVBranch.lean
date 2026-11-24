import YM.MergeProof.Summit
import YM.UVNext.FREE_STRESS_CERTIFICATE.Choose

/-! From the actual construction. Retain a *common* scaling curve, the
quotients and calculus used on both sides, and normalize the centered current
by the local generator test before going to OS/B. Comparison here is to the
zeroth (Maxwell) continuum comparator on these scales only. -/
set_option autoImplicit false
noncomputable section
namespace YM.PertExtension
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 500000
open Function Filter Set MeasureTheory Analysis Extraction Table Climb Org Cells Ward
open MergeProof.Acme Next.UVStress
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

private lemma currencies {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] {X : ℕ → Z} {x : Z}
    (k : ℝ) (f : ℕ → ℝ) (hx : Tendsto X atTop (𝓝 x)) (ht : Tendsto (fun i => f i • X i) atTop (𝓝 (k • x))) (h : x≠0) : Tendsto f atTop (𝓝 k) := by
  obtain ⟨Y,hY⟩ := Module.Projective.exists_dual_ne_zero ℝ h
  have hc := Y.continuous_of_finiteDimensional
  have he := hc.continuousAt.tendsto.comp ht; have hv := hc.continuousAt.tendsto.comp hx
  have hp := he.div hv hY
  rw [map_smul,smul_eq_mul, mul_div_cancel_right₀ _ hY] at hp
  apply hp.congr'
  filter_upwards [hv.eventually (isOpen_compl_singleton.mem_nhds hY)] with i hi
  change Y (f i • X i)/Y (X i)= _
  rw [map_smul, smul_eq_mul,mul_div_cancel_right₀ _ (show Y (X i) ≠ 0 from hi)]

variable {G : Gauge}

section
variable {C : Family G} {f : Order} {S : Table C.book} {E : DiffPlan S}
variable {I : IR (C:=C) S} {M : MaxwellData C} (p : UV C f S E M I) (X : Scaling S)
variable (hi : E.Inclusions S) (hD : E.Derivatives S) (hv : Approaches (path X) (isoPanel X))
    (hV : Stable p.basis.kernel.spin M.hT.spin E M.T.W X) (hx : X.meter I.J M.T.J)
local notation "h" => p.basis.kernel

include p hD hv hV hx
lemma conLap_scale {d Q R} {w : Scaling S → ℕ → ℝ} (hW : Bid.Watches I.J M.T p.basis.kernel.spin M.hT.spin E (fun X =>
    Bid.ConLap X (P:=Q) d R (w X))) (hw : ∀ Y m i, w (afterScale Y m) i=w Y (i+m)) :
    Bid.ConLap X Q d R (w X) := by
  obtain ⟨D,N,k,A,hA,ht⟩:=hW
  obtain ⟨m,hm⟩ := focused_track h hD M.hT M.T M.lit.pales X hv hV I.J hx N D k A hA
  have hz := ht (afterScale X m) D N k A le_rfl le_rfl le_rfl le_rfl hm
  apply tendsto_def.mpr; intro s hs
  change ∀ᶠ i : ℕ in atTop, w X i • X.aisle i d _ ∈ s
  specialize hz hs; obtain ⟨u,hu⟩ := eventually_atTop.mp hz
  filter_upwards [eventually_ge_atTop (u+m)] with i hi
  obtain ⟨v,rfl⟩:= Nat.exists_eq_add_of_le (show m ≤ i from by omega)
  specialize hu v (by omega)
  simp_rw [add_comm m v]
  change w _ _ • (afterScale X m).aisle v d _ ∈ s at hu
  rw [hw] at hu; exact hu

include hi
set_option backward.isDefEq.respectTransparency false in
lemma xi_reads (c : ℝ)(he : ∀ d, leaves I.p d=c • leaves E.deriv d) :
    Tendsto (fun i => c/X.xi i) atTop (𝓝 M.T.κ) := by
  have ht := Work.A04.answer h E hi hD M I.J 4; have hh := Work.A05.answer h E hi hD M I.J 4 I.p I.Y p.planet
  have hy : Bid.Watches I.J M.T p.basis.kernel.spin M.hT.spin E (fun X => Bid.ConLap X I.p 4 (M.T.κ • M.T.W.deriv) (fun i => X.r i/X.xi i)) := by
    obtain ⟨D,N,m,R,h1,h3⟩:= hh; exact ⟨D,N,m,R,h1,fun X d n k B h1 h2 h4 h5 hx => (h3 X d n k B h1 h2 h4 h5 hx).1⟩
  have hL := conLap_scale p X hD hv hV hx ht (fun _ m i => by rfl)
  have hq := conLap_scale p X hD hv hV hx hy (fun _ m i => by rfl)
  let v(i) := X.r i • (X.aisle i 4 (leaves E.deriv 4))
  refine currencies (X:=v) _ (fun i=> c/X.xi i) hL ?_ M.lit.born
  unfold Bid.ConLap at hq; rw [he,show leaves (M.T.κ • M.T.W.deriv) 4=M.T.κ • leaves M.T.W.deriv 4 from by ext1 j; ext1 k;rfl] at hq
  apply hq.congr; intro k
  simp_rw [map_smul,smul_smul]; unfold v; rw [smul_smul]; congr 1; ring
open UVNext.FreeStress

include hi in
lemma has_flow : leaves E.deriv 4 ≠ 0 := by
  have ht := conLap_scale p X hD hv hV hx (Work.A04.answer p.basis.kernel E hi hD M I.J 4) (fun _ m i=> by rfl)
  intro H; unfold Bid.ConLap at ht; rw [H] at ht; simp_rw [map_zero,show ∀ i, X.r i • (0:Climb.Vector 4 (Bel C.book))=0 from by intro i; ext1 j; ext1 k; change X.r i • (0:(Bel C.book).Field 5) = 0; exact smul_zero _] at ht
  apply M.lit.born
  exact tendsto_nhds_unique ht tendsto_const_nhds

set_option backward.isDefEq.respectTransparency false in
lemma centered_tensor {c : ℝ} {U} {J : S.Stress} (hF : FreeDiv M.T M.hT M.lit.hers) (hI : I.J∈KernelSpace p.basis.kernel.spin) (hn : I.J≠0)
    (hy : Tab S E M I p c U J) : Tensorial (mill M I c U) (((c:ℂ)⁻¹) • I.J) := by
  let jS := c⁻¹ • I.J; have hg : jS = (c:ℂ)⁻¹ • I.J := by unfold jS; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rw [← Complex.ofReal_inv]; rfl
  let V:=mill M I c U; have Hp := hy.locality.spots
  have hS := p.planet.tensor
  have ho : E.Orientation p.basis.kernel.spin := p.aligned
  have hQ := (differential_rank p.basis.kernel M.hT ho M.T M.lit.hers hF hD M.lit.pales X hv hV).2
  let j : KernelSpace p.basis.kernel.spin := ⟨jS, (KernelSpace p.basis.kernel.spin).smul_mem _ hI⟩
  let K := LinearMap.ker (currentDiv E p.basis.kernel.spin ho)
  let j' : K := ⟨j,(linear_cons ..).mpr (by change Conserved E p.basis.kernel.spin jS; rw [hg,← Complex.ofReal_inv]; exact Work.A15.conserved_real_smul I.J hS c⁻¹)⟩
  have hJ := hy.locality.conserved
  have hjv : reCenter S J∈ KernelSpace p.basis.kernel.spin := enters p.basis.kernel J (sym_mem.mpr ⟨hJ.symmetric,hJ.real,fun k a b=> by rw [← Hp.signed]; exact hy.locality.spin ..⟩)
  let hk : KernelSpace p.basis.kernel.spin := ⟨_,hjv⟩
  have htk : currentDiv E p.basis.kernel.spin ho hk=0 := by
      apply (linear_cons _ _ ho hk).2
      refine ⟨(sym_mem.mp (kernel_mem.mp hk.property).1).1,(sym_mem.mp (kernel_mem.mp hk.property).1).2.1,?_⟩
      intro b
      change ∑ a, E.deriv 4 a (centering S 4 _)=0
      have hd := E.unit_drop p.basis.kernel.laws hD p.basis.kernel.smooth 4
      simp only [value_center,map_sub,map_smul,hd,smul_zero,sub_zero,hJ.divergence]
  let Q:K := ⟨hk,htk⟩
  have he : j' ≠ 0 := fun e => smul_ne_zero (inv_ne_zero hy.Γ.positive) hn (congr_arg (fun v:K=>v.val.val) e)
  obtain ⟨a,ha⟩ := (finrank_eq_one_iff_of_nonzero' j' he).1 hQ Q
  have he : a • jS = reCenter S J := congr_arg (fun v:K=>v.val.val) ha
  have ha : a=1 := by
    have hB := has_flow p X hi hD hv hV hx
    let down (i j) := -expectation S 4 (J i j)
    have he' : reCenter S J = J+fossil down := by
       funext i j
       change centering S 4 (J i j) = J i j + down i j • S.unit 4
       rw [value_center]; simp [down,sub_eq_add_neg]
    change Conserved E p.basis.kernel.spin J at hJ
    have hz := add_unit p.basis.kernel hy.locality.charges down (fun i j => by dsimp [down]; rw [hJ.symmetric i j])
    rw [← he',← he] at hz
    have hg' : StressLaws S jS E.deriv V.lie := by rw [hg, ← Complex.ofReal_inv];exact Work.A15.normalize_flux p.basis.kernel I.J c hy.Γ rfl
    by_contra hh
    apply hB
    funext b
    apply ContinuousLinearMap.ext; intro i
    apply Table.field_ext S p.basis.kernel.laws.toSymmetric; intro n q x hx
    obtain ⟨χ,hχ⟩ := Work.A01.exists_window x hx
    change S.useAt S x (Fin.cons ⟨5,E.deriv 4 b i⟩ q) = S.useAt S x (Fin.cons ⟨5,0⟩ q)
    have heq := (hz.translation hx q hχ b 4 i).symm
    change S.useAt S x (Fin.cons ⟨5,E.deriv 4 b i⟩ q) = _ at heq
    rw [← Work.A15.translationFlux_apply hx hχ p.basis.kernel.smooth q,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,Work.A15.translationFlux_apply hx hχ p.basis.kernel.smooth q, hg'.translation hx q hχ b] at heq
    change S.useAt S x (Fin.cons ⟨5,E.deriv 4 b i⟩ q) = (a:ℂ)*S.useAt S x (Fin.cons ⟨5,E.deriv 4 b i⟩ q) at heq
    rw [← Work.A01.front_eval q x _ 0,map_zero]
    apply (mul_eq_zero.mp (by rw [sub_mul,one_mul, ← heq,sub_self] : ((a:ℂ)-1)*_ = 0)).resolve_left
    intro e; apply hh;exact_mod_cast (sub_eq_zero.mp e)
  have hZ := stays_tensor p.basis.kernel Hp hy.locality.motion hy.locality.spin
  simpa [← he,ha,hg] using hZ
lemma stressTends {c : ℝ} {U} {J : S.Stress} (hy : Tab S E M I p c U J) (a b) :
    Tendsto (fun k => (X.U k 4).symm ((↑(X.r k^4):ℂ) • (((c:ℂ)⁻¹ • I.J : S.Stress) a b))) atTop (𝓝 ((↑(M.T.κ⁻¹) : ℂ) • (M.T.J a b))) := by
  apply Tendsto.congr' (f₁:=fun k=> (↑(c/X.xi k : ℝ)⁻¹ : ℂ) • ((X.U k 4).symm ((↑((X.xi k)⁻¹*X.r k^4):ℂ) • I.J a b))) (Eventually.of_forall ?_)
    ((Complex.ofRealCLM.continuous.continuousAt).tendsto.comp (Tendsto.inv₀ (xi_reads p X hi hD hv hV hx c hy.Γ.sizes) M.T.hκ) |>.smul (hx a b)) -- syntax
  intro k
  rw [show ((c:ℂ)⁻¹ • I.J : S.Stress) a b = (c:ℂ)⁻¹ • I.J a b from rfl,smul_smul]; simp only []; rw [← map_smul,smul_smul]
  congr 2
  push_cast
  have ht := X.sign k
  have he : (↑(X.xi k):ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp

set_option backward.isDefEq.respectTransparency false in
lemma relevant (hF : FreeDiv M.T M.hT M.lit.hers) (hI : I.J∈KernelSpace p.basis.kernel.spin) (hn : I.J≠0)
    (HY : Spec.Calibrated C) :
    ∃ q : Spec.Final C f S, q.room=p.basis ∧ q.sector.derivatives=E ∧
      ∀ a b, Tendsto (fun k => (X.U k 4).symm ((↑(X.r k^4):ℂ) • (q.sector.energy a b))) atTop (𝓝 ((↑(M.T.κ⁻¹) : ℂ) • (M.T.J a b))) := by
  have ht := Bid.station M E I p YM.Outer.miles Work.A01.answer Work.A02.answer Work.A03.answer
    Work.A04.answer Work.A05.answer Work.A06.answer Work.A07.answer Work.A08.answer
    Work.A09.answer Work.A10.answer Work.A11.answer Work.A13.answer Work.A14.answer
    Work.A15.answer Work.A16.answer Work.A17.answer
  obtain ⟨c,U,J,hab,K,hK⟩ := ht.picks E M I p hi hD
  let T : Spec.Algebra S := ⟨E,mill M I c U,(c:ℂ)⁻¹ • I.J⟩
  have hLoc := hab.locality
  have hS : Spec.Locals T p.basis.kernel.spin :=
    { hLoc with
      conserved := by dsimp only [T]; rw [← Complex.ofReal_inv]; exact Work.A15.conserved_real_smul I.J p.planet.tensor c⁻¹
      spin := centered_tensor p X hi hD hv hV hx hF hI hn hab
      charges := by
        dsimp only [T]; rw [← Complex.ofReal_inv]; exact Work.A15.normalize_flux p.basis.kernel I.J c hab.Γ rfl }
  have he := Bid.Looms YM.Next.Phase.seats Work.B01.answer Work.B02.answer Work.B03.answer Work.B04.answer
    Work.B05.answer Work.B06.answer Work.B07.answer Work.B08.answer Work.B09.answer
    Work.B10.answer Work.B11.answer Work.B12.answer Work.B13.answer Work.B14.answer
    Work.B15.answer Work.B16.answer Work.B17.answer Work.B18.answer p.tables p.basis T
  obtain ⟨α, hα⟩ := he.cleanse hS
  obtain ⟨x, y, Z, hZ, hy, hu, hw⟩ := YM.Next.BOUNDARY.after_materializes (s:=p.basis) hα K hK
  exact ⟨⟨HY,p.basis,T,α,hα,x,y,Z,hy⟩,rfl,rfl,stressTends p X hi hD hv hV hx hab⟩

end

open UVNext.FreeStress

/-- Receipts on *same* unselected hierarchy/sectors, including the positive-stage
fields with eventual signed/real/unit/inclusion alignment through each requested
horizon and translation-normalized weak stress (scales approaching UV). `M.T.W` and
rotation/stress data on comparator are kept. No assertion of comparison on scales not
sampling the path X.r, or convergence rate. -/
structure Actual (C : Family G) (f : Order) (S : Table C.book) where
  F : Spec.Final C f S
  E : DiffPlan S
  same : F.sector.derivatives=E
  incl : E.Inclusions S
  diff : E.Derivatives S
  M : MaxwellData C
  I : IR (C:=C) S -- I.J unnormalized
  uv : UV C f S E M I
  nonzero : I.J≠0
  zero_v : I.J∈KernelSpace uv.basis.kernel.spin
  curve : Scaling S
  approaches : Approaches (path curve) (isoPanel curve)
  aligned : Stable F.room.kernel.spin M.hT.spin E M.T.W curve
  calibrated : curve.meter I.J M.T.J
  free_stress : M.T.J = torch C.book.grid 1
  free_rank : FreeDiv M.T M.hT M.lit.hers
  stress (a b : Axis) : Tendsto (fun k => (curve.U k 4).symm ((↑(curve.r k^4):ℂ) • (F.sector.energy a b))) atTop (𝓝 ((↑(M.T.κ⁻¹) : ℂ) • (M.T.J a b)))

namespace Actual
variable {C : Family G} {f : Order} {S : Table C.book}
lemma jets (A : Actual C f S) (N d k : ℕ) (R : ℝ) (hr : 0<R) : A.curve.jets N d k R :=
  comparison_jets A.uv.basis.kernel A.diff A.M.hT A.M.lit.pales A.curve A.approaches N d k R hr
end Actual

-- Following Acme.xanadu and emanate but fixing the scaling curve in the endpoint.
theorem temple (h : G.Simple) (b : ℝ) (hb : 0 < b) (f : Extraction.Order) :∃ C:Family G,C.Makes∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=b ∧ Extraction.Wcmain C ∧ ∃ (g:Extraction.Order) (S:Table C.book), Nonempty (Actual C (f.refine g) S):=by
    obtain ⟨C,hB,hC,hM,hW,H,hQ,hF⟩:= YM.PhysicalNext.Repeat.Legato.noel h hb
    obtain ⟨g,A,L,R,S,E,hA,s,hN⟩:= hF f
    obtain ⟨hs,hG⟩:= hQ (f.refine g) s.copies
    obtain ⟨T₀,_,_⟩:= Maxwell.Free.maxwell_supplies C h 1 one_ne_zero
    obtain ⟨M, hstress, _, _, _, _, _, hd⟩ := YM.UVNext.FreeStress.fire h T₀ 1 one_ne_zero
    have hh := M.hT.smooth
    have hS := realizes_stations s.cutoff s.generic s.ordered s.kernel.smooth hh M.hT.spin (fun N D R hr=> hG N D R (zero_lt_one.trans_le hr) hh _)
    obtain ⟨hf,I,X,hI,hX,hY,hZ,hL,hp,ha⟩ := readyA s.cutoff s.ordered s.generic s.kernel s.copies hA.clean.ready hA.clean.tilt (cap_given s.corrected) M.T M.hT M.lit.edges M.lit.pales M.lit.hers hd hS H
    have p: UV C (f.refine g) S E M I := ⟨s,hf,hp,ha,hs⟩
    obtain ⟨F,-,ht,hT⟩:= relevant p X hA.clean.ready hA.clean.tilt hY hZ hL hd hX hI hC
    exact ⟨C,hM,hC,hB,hW,g,S,⟨F,E,ht,hA.clean.ready,hA.clean.tilt,M,I,p,hI,hX,X,hY,hZ,hL,hstress,hd,hT⟩⟩
end YM.PertExtension
