import YM.LocalLTE.Roost.Counter
import YM.LocalLTE.Units.Sure
/-! Each paying Primitive. Substitutions through high extension. Economy Himself. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Vine
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen Frond Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
variable {v z r W s y η γ B : ℝ} {j n m : ℕ}
lemma atom_brush {E':Type}[NormedAddCommGroup E'][NormedSpace ℝ E'] (A: Atom G n) (U:E'→ Config G c)(w:Site c){x:E'}(h:Mode U x j s)(hh:A.length≤ m) : Brush j (A.magnitude* (royalty G^2)^n) ((n:ℝ) * (2*m*(s*royalty G))) (fun x=> A.unmasked (U x) w) x :=by
  let a (i:Fin n)(x:E') := (A.leg i).atSite (U x) w; let R:=royalty G; let s':= 2*m*(s*R); have ht:0≤ s*R:=mul_nonneg h.pos (zero_le_one.trans (royalty_ge G))
  have hs' : 0≤ s':= mul_nonneg (by positivity) ht
  have ha (i:Fin n): Brush j (R^2) s' (a i) x:= (slot_cost (A.leg i) w h.pos h.atLink).climb le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast ((single_le_sum (f:=fun i=>(A.leg i).length) (fun _ _=>Nat.zero_le _) (mem_univ i)).trans hh)) (by norm_num)) ht)
  let f (k:Fin n→ G.ColorIndex) x:= ∏ i:Fin n, (a i x) (k i); have hf (k:Fin n→G.ColorIndex): Brush j ((R^2)^n) (n*s') (f k) x:= by
    have hx:= Brush.all_prod (univ:Finset (Fin n)) (fun i y=> (a i y) (k i)) (fun _=> R^2) (fun _=>s') (fun i _=> colorEvaluated (k i) (ha i)); simpa only [prod_const,Fintype.card_fin,sum_const,nsmul_eq_mul,card_univ] using! hx
  let p k:= ‖A.coeff k‖ * (R^2)^n; have hp k (_hk:k∈ (univ:Finset (Fin n→G.ColorIndex))): Brush j (p k) (n*s') (((A.coeff k:ℝ)) • (f k)) x:= (hf k).smul _
  refine (Brush.spree _ _ _ (by positivity) hp).climb ?_ le_rfl; simp only [p,Real.norm_eq_abs, Atom.magnitude, Finset.sum_mul] -- edit
  exact le_rfl

def atomΛ (X:Coat T F) (A : ℕ→ Atom G m) (p:Trans f)(b:ℝ)(z:Air f G)(x:Disk G c):= b*(A p.2.2).unmasked (pull p.1 0 (inputΛ X z x)) p.2.1
lemma tassels {P:Teller G}(L:Side)(D:Patch)(hd:D.Branches P.bind G){d p w N:ℝ→ℝ}(Q:YM.ConnectedActivityE6.Target G P){W:ℝ}(o:Target.Order G W)(j m:ℕ)(h₁:1≤j){v e:ℝ}(hW: -(1/2:ℝ) ≤ v)(h: v<0)(hp: Rate G L v p)(hp': ∀ᶠ x:ℝ in atTop,0≤p x)(hw:Rate G L e w)(hk:Rate G L 0 d)(hN:Rate G L 0 N):∃ V :ℝ→ℝ, Rate G L e V ∧ ∀ᶠ t in atTop,
    ∀ (c f:Side)(S:StepData c f)(T:Tube G S) (A:ℕ→ Atom G m), S.patch=D → ∀ μ α:ℝ, Target.GrantBodies W t μ L Q o α T → ∀ (F: Forest S.ratio) (X : Coat T F), X.x=t → X.width=o.K →∀ z: Air f G,(∀ i, |z i| ≤ |d t|)→∀ x: Disk G c,‖x‖≤p t → ∀ (i:Trans f)(b:ℝ), ((A i.2.2).length:ℝ)≤N t→ |b|≤ w t → Brush j ((A i.2.2).magnitude*|V t|) 1 (atomΛ X A i b z) x:=by
  obtain ⟨A,C,R,hA,hC,hR,H⟩:= thistles L D hd Q W o j h₁ hW h hp hk hp'
  let u:= royalty G; let S t:= 2*N t*(|R t| *u); let V t:= w t*((u^2)^m)*(1+(m:ℝ)*S t)^j
  have hv : Rate G L 0 S:= by simpa only [add_zero] using! ((hN.mul_left 2).mul ((hR.compare (v:=fun x=>|R x|) (Eventually.of_forall fun x=>(abs_abs _).le)).mul_right u))
  refine ⟨V,(by simpa only [zero_mul,add_zero] using! ((hw.mul_right _).mul (((Rate.const 1).add (hv.mul_left m)).pow j))),H.mono ?_⟩
  intro t ht c f S' T A hD μ α H F X hx hX z hz x h i b hI hb
  let a:= A i.2.2; have hU:= Blaze.turn (ht c f S' T hD _ _ H F X hx hX z hz x h|>.2.2) i.1
  have hp : Brush j (a.magnitude*(u^2)^m) (m*S t) _ x := (atom_brush a _ i.2.1 hU le_rfl).climb le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hI (by norm_num)) (mul_nonneg (abs_nonneg _) (zero_le_one.trans (royalty_ge _)))) (Nat.cast_nonneg _))
  apply (hp.trim.smul b).climb _ le_rfl; change |b| *_ ≤ _
  have hz:0≤a.magnitude:= sum_nonneg fun _ _=>abs_nonneg _
  exact (mul_le_mul_of_nonneg_right hb hp.trim.nonneg).trans ((le_of_eq (by ring : w t*((a.magnitude*(u^2)^m)*(1+(m:ℝ)*S t)^j)= a.magnitude*(w t*((u^2)^m)*(1+(m:ℝ)*S t)^j))).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hz))
-- Plug-in regular E6, restore chart. Need annotate m ≤ D_in.
lemma field_fuel {P:Teller G}(L:Side)(D:Patch)(hd:D.Branches P.bind G){d p :ℝ→ℝ}{N : ℝ→ℕ}(Q:YM.ConnectedActivityE6.Target G P){W:ℝ} (o:Target.Order G W)(j m:ℕ)(h₁:1≤j){v κ k:ℝ}(hW: -(1/2:ℝ) ≤ v)(h: v<0)(hp: Rate G L v p)(hp': ∀ᶠ x:ℝ in atTop,0≤p x)(hR:Reliable G κ k)(hk:Rate G L 0 d)(hN:Rate G L 0 fun t=>(N t:ℝ)):∃ V :ℝ→ℝ, Rate G L ((1/2:ℝ)*m) V ∧ ∀ᶠ t in atTop,
    ∀ (c f:Side)(S:StepData c f)(T:Tube G S), S.patch=D → ∀ μ α:ℝ, Target.GrantBodies W t μ L Q o α T → ∀ (F: Forest S.ratio) (X : Coat T F), X.x=t → X.width=o.K →∀ z: Air f G,(∀ i, |z i| ≤ |d t|)→∀ x: Disk G c,‖x‖<p t → ∀ (y:Site f)(i:ℕ)(Y': Config G f→ℝ)(B:BudgetPoint)(e:ℝ), i≤N t→ LocalLTE.FrameBox.Polynomial i κ y m Y' → B.threshold=Pressure.fiery G t L →(∃ s:Support f, B.supBounds y s Y' e) → Brush j (e *|V t|) 1 (Y' ∘ inputΛ X z) x:=by
  obtain ⟨A,C₀,R,hA,hC,hQ,H⟩:= thistles L D hd Q W o j h₁ hW h hp hk hp'
  obtain ⟨J,hJ,hV⟩:= LocalLTE.FrameBox.supply G m j hR
  obtain ⟨M,r,hM,hr,hL⟩:= chord_chart_cost G
  obtain ⟨Y,R',hP'⟩:=Frond.cleanly G j 1 zero_lt_one
  -- hP': Suitable G j Y R' 1
  have hq':0 ≤ Y:= (hP'.sound (1:G.El) (by rw [G.mat_one,sub_self,norm_zero]; exact hP'.pos.le)).nonneg -- edit
  let z t:=M*|A t| + M*|A t|; let P t:= (8*(N t:ℝ)+1)*z t; let v' (t:ℝ):=(1+royalty G)*(LocalLTE.Frame.expense G (N t) (|R t|))
  have hq:= hA.compare (v:=fun x=>|A x|) (Eventually.of_forall fun x=> (abs_abs _).le); have hv:Rate G L v P:= by unfold P; simpa only [zero_add] using! (((hN.mul_left 8).add (Rate.const 1)).mul ((hq.mul_left M).add (hq.mul_left M)))
  let V₀:ℝ:=1+j.factorial*Y; let Θ t:= (Pressure.fiery G t L)⁻¹; let V t:= J*Θ t^m*V₀^m*(1+m*v' t)^j
  have he':=(hQ.compare (v:=fun x=> |R x|) (Eventually.of_forall fun _=> (abs_abs _).le)); have hu : Rate G L 0 v':= by
    let B x:=4*(N x:ℝ)*(|R x| *royalty G); have hg:Rate G L 0 B:= by simpa only [add_zero] using! ((hN.mul_left 4).mul (he'.mul_right _))
    unfold v' LocalLTE.Frame.expense; exact ((hg.mul_right _).add ((he'.mul_right _).add hg)).mul_left _
  refine ⟨V,?_,?_⟩
  · simpa only [zero_mul,add_zero] using! (((((inverse_mist G L).pow m).mul_left J).mul_right _).mul (((Rate.const 1).add (hu.mul_left m)).pow j))
  filter_upwards [H,hA.below h _ hr,hv.below h _ hR.down,(hv.mul_left G.colorScale).below h _ hP'.pos] with t ht hv' hk' hK c f S T hS μ α H F X ht' hX z' hz x hx y i Q' B e he hΘ hBt hB
  let U:=inputΛ X z'; let s:= p t; have hp:=ht c f S T hS _ _ H F X ht' hX z' hz
  have hh x (hx:‖x‖≤p t) (i:Bond f): G.chord (U x i)≤ z t:= by
    let v:= twig X z' x; let V:=increment 1 v.1
    have hT:‖v.1‖≤ |A t| ∧ ‖v.2‖≤|A t|:=max_le_iff.mp ((hp x hx).1:‖v‖≤_)
    have hv (i:Bond f): G.chord (replica S.ratio (V:Config G c) i) ≤ M*|A t| := by
      unfold replica; split; next => rw [G.chord_one]; positivity
      next =>
        let j:=S.ratio.parent i.1; let k:Bond c:=(j,i.2)
        change G.chord (increment (1:Config G c) v.1 k) ≤ _; rw [increment,Pi.one_apply,mul_one]; exact (hL _ (((norm_le_pi_norm ..).trans hT.1).trans hv')).trans (mul_le_mul_of_nonneg_left ((norm_le_pi_norm ..).trans hT.1) hM.le) -- parent? neg case
    exact (G.chord_triangle (G.lieExp (v.2 i)) (replica S.ratio V i)).trans (add_le_add ((hL _ (((norm_le_pi_norm ..).trans hT.2).trans hv')).trans (mul_le_mul_of_nonneg_left ((norm_le_pi_norm ..).trans hT.2) hM.le)) (hv _))
  obtain ⟨s,hZ⟩:= hB
  obtain ⟨Y',Q₀,rfl⟩:= hΘ
  let r:= |R t|; have hp:(8*i+1:ℝ)* z t ≤ P t:= by unfold P; gcongr
  have hΨ : Brush j V₀ (v' t) (LocalLTE.FrameBox.Grove.crook Y' i Chi.canonical κ ∘ U) x:=
    (LocalLTE.FrameBox.climbs Y' hR i (ht c f S T hS _ _ H F X ht' hX z' hz x hx.le|>.2.2) hP'
       (by filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hx)] with v hv; exact hh v hv.le) hq' (show 0≤ z t from by unfold z; positivity) (hp.trans ((le_abs_self _).trans hk')) ((mul_le_mul_of_nonneg_left hp G.colorScale_pos.le).trans ((le_abs_self _).trans hK))).climb (le_add_of_nonneg_left zero_le_one) (by unfold v' LocalLTE.Frame.expense; have hg:=royalty_ge G; gcongr)
  have hr:= hV _ i B y Y' Q₀ e _ s hZ V₀ (v' t) (le_add_of_nonneg_right (by positivity)) hΨ.pos _ _ x hΨ
  apply Brush.shimmy (hr.trim.climb ?_ le_rfl) (Eventually.of_forall fun x=>?_)
  · rw [hBt]; change J*e*Θ t^m*V₀^m* (1+ (m:ℝ)*v' t)^j≤e*|V t|
    exact (le_of_eq (by unfold V; ring : _ = e* V t)).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hZ.1)
  change LocalLTE.Cabana.actual Q₀ _=LocalLTE.Cabana.actual (LocalLTE.FrameBox.clear Y' i Q₀) (Y'.crook i _ _ _); rw [LocalLTE.FrameBox.rays]; unfold LocalLTE.FrameBox.Grove.crook; rw [Y'.range_id]
end YM.ConnectedActivityE6.Blaze.Vine
