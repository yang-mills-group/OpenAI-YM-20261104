import YM.LocalLTE.Roost.Keel
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Dryland
/-! Archive for analytic excursions with Y.δ. File based on Dryland. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Vine
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
open Brush Foramen Frond Gate Scroll Vine Tablet Metric
variable {v z r Q s y η γ : ℝ} {j m : ℕ} {U : E → Config G c} {x : E}

private lemma tugs (X : Coat T F) (h : P.Funds S T) (i : Mention c f) (p : Directions G f) (hv : X.selected i.1 (spot S i.2)) :
    strain X i.1 i.2 p = strain X i.1 i.2 0 + X.motion p i := by
  obtain ⟨_,_,hk,-⟩:=h.feeds
  obtain ⟨L,H⟩ := SliceRows.linear T X.R hk i.1 i.2 X.V
  unfold strain Coat.motion Coat.signal; rw [if_pos hv,X.lens_zero,add_zero, ← H,← H,← H,map_add,add_assoc]

private lemma freeWorld {u : ZipP G c f} (W : ℝ) (h : Room P S T s) (X : Coat T F) (_hx : X.x=s) (hc : ‖u‖ ≤ W)
    (i : Mention c f)
    (hp : ∀ k p z, ‖z‖≤W→ Brush j r 1 (fun u:ZipP G c f=> Scroll.freely T X.x (increment 1 u.1) k p) z) :
    Brush j r 1 (fun v=> strain (dry X v) i.1 i.2 0) u := by
  let L:= (reachP i.1 G c f).toContinuousLinearMap
  have hh v : ‖L v‖≤ ‖v‖ := max_le ((displacement_bounded i.1 1 v.1).trans (le_max_left ..)) (by change ‖(0:Directions G f)‖≤_; simp)
  have he := Brush.reading L (hp (choice i.1 X.k) i.2 (L u) ((hh u).trans hc)) (e:=1) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=> by rw [one_mul]; exact hh i)
  rw [mul_one] at he; simp_rw [sprig X _ _ h.accepted]; exact he

lemma driftless (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (j : ℕ) (hj : 1≤j) {V : ℝ → ℝ}
    {ξ:ℝ}(hξ:ξ<0)(h : Rate G L ξ V) (hv : ∀ᶠ x in atTop,0 ≤ V x) {η r Q : ℝ} (hT : Torch η r Q) :
    ∃ P₀ E : ℝ → ℝ, Rate G L 0 P₀ ∧ Rate G L 0 E ∧ ∀ᶠ s in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S),
      S.patch=D → Works P L s S T→ ∀ (F : Forest S.ratio) (X : Coat T F), X.x=s→
      Allow X.blank.plate (along S) (tubularPrice G L) η r Q → ∀ x: ZipP G c f,
        ‖x‖≤V s → Brush j (P₀ s) 1 (voltage ∘ dry X) x∧ ∀ i : Mention c f, Brush j (E s) 1 (fun v=> strain (dry X v) i.1 i.2 (voltage (dry X v))) x := by
  obtain ⟨A,e,p,Y,W,hU₁,hY,HZ,HR⟩ := lofty P L D hD j hj hξ h hv η r Q hT
  obtain ⟨R,h₁,Z,h₂,hz,hK⟩ := Gate.beam P L D hD j
  let b := min e (retain e p A)
  let m:= tubularPrice G L; let q x := ‖Coat.scale‖*Z x
  let H x:= facePrice j (radiusB x) m A (payE e p A m)
  let Q' x:= H x*(Y*q x); let v x:= driftP j (W x)+(W x+1); let K (x:ℝ):= (Fintype.card G.ColorIndex:ℝ)*
    (‖Coat.scale⁻¹‖*(Y*Q' x)*(1+(W x+v x))^j)
  have hV := ((polynomial G L j m A (payE e p A m)).mul ((hz.mul_left ‖Coat.scale‖).mul_left Y))
  have hp:= Rate.const (G:=G) (L:=L) (1:ℝ)
  let p₀ x:= ((Fintype.card G.ColorIndex:ℝ)*Q' x)*(1+v x)^j
  refine ⟨p₀,fun x=> Z x+K x,?_,hz.add ?_,?_⟩
  · have hv : Rate G L (0:ℝ) v := (HZ.mul_left _).add (HZ.add hp)
    exact show Rate _ _ 0 (fun x=>((Fintype.card G.ColorIndex:ℝ)*Q' x)*(1+v x)^j) from (by simpa only [zero_mul,zero_add] using! ((hV.mul_left _).mul ((hp.add hv).pow j)))
  · have hv : Rate G L (0:ℝ) v := (HZ.mul_left _).add (HZ.add hp)
    unfold K; simp_rw [mul_assoc (‖Coat.scale⁻¹‖)]
    simpa only [zero_mul,zero_add] using! ((((hV.mul_left Y).mul ((hp.add (HZ.add hv)).pow j)).mul_left _).mul_left _)
  filter_upwards [HR,hK,room G P L,h.below hξ _ h₁] with
    s hr hF hU hs c f S T heq ht F X hx hp x hy
  let X₀ := dry X x
  subst s
  obtain ⟨ha,hP₀,hA⟩:= hr c f S T heq ht F X rfl hp x hy
  have hf := hU c f S T ht
  let T x:=dry X x
  have hu (l : ZipP G c f) (i : Mention c f) : (T l).selected i.1 (spot S i.2) := X.blank_all i.1 (spot S i.2)
  have hZ' i := freeWorld R hf X rfl (hy.trans ((le_abs_self _).trans hs)) i (hF _ _ _ _ heq ht)
  have hB (p: Coat.Target c f G): Brush j (q X.x) 1 (fun v=> stand (bar (dry X v) 0) p) x := by
    simp only [stand, bar]; simp_rw [show ∀ v, (if (dry X v).selected p.1.1 (spot S p.1.2) then _ else 0) = Coat.scale • strain (dry X v) p.1.1 p.1.2 0 from fun v=> if_pos (hu v p.1)]
    exact colorEvaluated _ ((hZ' p.1).smul Coat.scale)
  have hn : 0 ≤ q X.x := mul_nonneg (norm_nonneg _) (hZ' (1,.inr (0,0))).nonneg
  have hM j := beam_vec hA.reverse hn zero_le_one hB j
  have hh : 0≤ b := (lt_min hU₁.hot ha.weather.1).le
  have hV:= padjets X.shutter (hP₀.tilt le_rfl le_rfl hh (min_le_left ..)) ha (min_le_right ..)
  let f' q (i:Tubular f G) := (well (T q)) i
  have he i : Brush _ (Q' X.x) (v X.x) (f:=fun z=> f' z i) x := (beam_vec
    (u:=fun v=>leanB (dry X v)) hV.reverse (mul_nonneg hY hn) (add_nonneg hA.pos zero_le_one) hM i).opposite
  have hq : 0≤ Q' X.x := mul_nonneg hV.basis (mul_nonneg hY hn)
  have hj : 0 ≤ v X.x := add_nonneg hV.pos (add_nonneg hA.pos zero_le_one)
  obtain ⟨w,z,hk,-⟩:=ht.funds.feeds
  refine ⟨(Brush.fold hj (mul_nonneg (Nat.cast_nonneg _) hq) ?_).trim,fun i=>?_⟩
  · exact fun i=> tie G _ hq hj fun j=> he (i,j)
  simp_rw [show ∀ q,strain (dry X q) i.1 i.2 (voltage (dry X q))=strain (dry X q) i.1 i.2 0+(dry X q).motion (voltage (dry X q)) i from fun q=> tugs _ ht.funds i _ (hu q _)]
  refine (hZ' i).gathering (tie G _ ?_ zero_le_one ?_)
  · exact mul_nonneg (mul_nonneg (norm_nonneg _) (mul_nonneg hY hq)) (pow_nonneg (add_nonneg zero_le_one (add_nonneg hA.pos hj)) _)
  intro j
  have hp i (z : ZipP G c f) : stand ((T z).motion (voltage (T z))) i=Coat.scale⁻¹*((T z).form *ᵥ f' z) i := by
    rw [show (T z).form *ᵥ f' z=(T z).form *ᵥ stand (voltage (T z)) from rfl,← Coat.charged_for _ hk]; field_simp [Coat.scale_pos.ne']
  change Brush _ _ _ (fun v=>stand _ (i,j)) x; simp_rw [← show ∀ z:ZipP G c f, T z=dry X z from fun _ => rfl, hp]
  exact ((beam_vec hA hq hj he (i,j)).smul (Coat.scale)⁻¹).trim
end YM.ConnectedActivityE6.Blaze.Vine
