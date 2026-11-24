import YM.LocalLTE.Roost.Thatch
import YM.LocalLTE.Roost.Nectar
/-! Loft Φ determinant bills. Charged at punched marginal using actual Brush tag. Halo exponent. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Vine
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
open Brush Foramen Frond Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond
variable {v z r Q W s y η γ : ℝ} {j m : ℕ} {U : E → Config G c} {x : E}
lemma admits (X : Coat T F) (h : Allow X.plate (along S) (tubularPrice G L) η r Q) (I : Finset (Tubular f G)) (hp : Window.distPay η r Q (tubularPrice G L) X.B ≤ Q⁻¹/2): let m:=tubularPrice G L; Allow (Pond.circuit I X.relating) (along S ∘ (fun v:↥I=>v.val)) m
      (retain η r Q) (Q⁻¹/2) (1+payE η r Q m) := by
  intro m; have hx:Allow X.relating (along S) m (retain η r Q) (Q⁻¹/2) (1+payE η r Q m) := ⟨h.census,Window.twin ..,h.weather.1,
    half_pos (inv_pos.mpr h.fuel),add_pos_of_pos_of_nonneg zero_lt_one h.disc,
    ((Control.increase (h.mate X.shutter) le_rfl (le_add_of_nonneg_left zero_le_one))).1,h.ground_C X.shutter hp⟩
  exact hx.sub (Embedding.subtype (fun z=> z∈I))
lemma pleasing (X : Coat T F) (I : Finset (Tubular f G)) (U:E→ ZipP G c f) (h : Allow (dry X (U x)).plate (along S) (tubularPrice G L) η r Q)
    (hp : Tablet j 0 v s (fun i=> (dry X (U i)).plate) (along S) (along S) x) :
    let a:=along S ∘ (fun v:↥I=>v.val)
    Tablet j 0 (facePrice j X.B (tubularPrice G L) v (payE η r Q (tubularPrice G L))) (driftP j s)
      (fun u=> Pond.circuit I (dry X (U u)).relating) a a x := by
  intro a; have he:= Foramen.padjets X.shutter hp h h.weather.1.le
  let p:= (Embedding.subtype (fun z:Tubular f G=> z∈I))
  have hh := (((he.joined he.reverse).scalar (1/2:ℝ)).trim_left (K:=p) (X:=p))
  apply hh.tilt _ le_rfl le_rfl le_rfl
  rw [Real.norm_eq_abs,abs_of_nonneg (by norm_num : 0 ≤ (1/2:ℝ))]; apply le_of_eq; ring
-- counting structure ℝ budgets reused. Δ fixed, rate0
private def vogueQ (j:ℕ)(F W d q N v:ℝ) := let b:= token j d q
    let c:= N; let D:= driftP j v
    let k := ((↑(j+1:ℕ):ℝ)*(1+c)^j)*(j.factorial*(1+(d*q+1)*(1+v)^j)^j)
    let z := (j.factorial*F)*(1+(1+k)*j)^j
    let r := (c*(W*(b*W)))*(1+(1+(D+1)))^j
    z+(r+r)
private lemma vogueRate {W N d v : ℝ→ℝ} (F Q:ℝ)(hW: Rate G L 0 W)(hN: Rate G L 0 N)(hd:Rate G L 0 d)(hp:Rate G L 0 v)(j:ℕ) : Rate G L 0 (fun x:ℝ=> vogueQ j F (W x) (d x) Q (N x) (v x)):=by
  have hz f (h:Rate G L 0 f): Rate G L 0 (fun x=>f x^j):=by simpa only [zero_mul] using h.pow j
  have hM f g (h:Rate G L 0 f)(hp:Rate G L 0 g): Rate G L 0 (fun x=>f x*g x):=by simpa only [add_zero] using h.mul hp
  have h:= Rate.const (G:=G) (L:=L) (1:ℝ)
  let k x := (↑(j+1:ℕ)*(1+N x)^j)*(j.factorial*(1+(d x*Q+1)*(1+v x)^j)^j)
  have hk : Rate G L 0 k:= hM _ _ ((hz _ (h.add hN)).mul_left _) ((hz _ (h.add (hM _ _ ((hd.mul_right Q).add h) (hz _ (h.add hp))))).mul_left _)
  let u x:= N x*(W x*(token j (d x) Q *W x))*(1+(1+(driftP j (v x)+1)))^j
  have hv:= hp.mul_left (↑j); have hu : Rate G L 0 u:=hM _ _ (hM _ _ hN (hM _ _ hW (hM _ _ (tokens G L hd j Q) hW))) (hz _ (h.add (h.add (hv.add h))))
  exact ((hz _ (h.add ((h.add hk).mul_right j))).mul_left _).add (hu.add hu)
private lemma vogueC {C n : ℝ} (hQ:0≤Q)(hp:0≤ W)(hC:0≤C)(hn: C≤ n)(hr:0≤r)(hv:0≤v)(hy:0≤ y): vogueQ j Q W r y C v≤ vogueQ j Q W r y n v := by
 unfold vogueQ; dsimp only
 have hk:0≤ token j r y:=by unfold token; exact sum_nonneg fun i _=> by change 0≤ (r*y+1)^_*y; positivity
 have ho:0≤ driftP j v:=mul_nonneg (Nat.cast_nonneg _) hv
 gcongr
-- Fixed log quotient. need 1 derivative; moreover F close.
def planeQ (X : Coat T F)(I:Finset (Tubular f G))(p:ZipP G c f):= circuit I (dry X p).relating
def pledgeΛ (X : Coat T F)(I:Finset (Tubular f G))(q:Body (↥I))(p:ZipP G c f):= lens₀ (planeQ X I p) q/lens₀ (planeQ X I 0) q
private lemma frameRise {j : ℕ}{ι:Type}[Fintype ι][DecidableEq ι]{C':E→Matrix ι ι ℝ} {Ω:E→Body ι} {p K₀ J:ℝ}{z:E}(h₁:1≤j)(hZ:‖z‖≤p)(hv:K₀*p≤1)(hP:∀ x∈Set.Icc (-1:ℝ) 1,Brush j J 1 Real.exp x) (hy:∀ i:E, i∈ closedBall 0 p → (C' i).PosDef ∧ Brush j K₀ 1 (frack C' Ω i) i) : Brush j ((↑j.factorial*J)*(1+(1+(K₀+1))*1)^j) 1 (fun x=> lens₀ (C' x) (Ω x)/lens₀ (C' 0) (Ω 0)) z∧ (C' z).PosDef:= by
  have h₀: (0:E) ∈ (closedBall 0 p):= mem_closedBall_self ((norm_nonneg _).trans hZ); have he:z∈(closedBall 0 p) := mem_closedBall_zero_iff.mpr hZ
  let g:= frack C' Ω 0
  have hS i (_hi:i∈(closedBall 0 p)): (fun v=> frack C' Ω i v+g i)=g := by funext b; unfold g; rw [Flux.sets 0]; ring -- edit
  have hb i (hi:i∈(closedBall 0 p)): Brush j (K₀+‖g i‖) 1 g i := by
    have hp := hS i hi
    exact Brush.shimmy (((hy i hi).2).gathering (Brush.certified zero_le_one (g i))) (Eventually.of_forall fun x=>congr_fun hp.symm x)
  have hx i (hi:i∈(closedBall 0 p)): ‖fderiv ℝ g i‖≤K₀ := by
     let Q:=frack C' Ω i; have hK:‖fderiv ℝ Q i‖≤K₀:= by simpa only [normJ,pow_one,norm_iteratedFDeriv_one,mul_one] using (hy i hi).2.order 1 h₁
     have he: fderiv ℝ g i=fderiv ℝ Q i := by
       have hp : (fderiv ℝ (fun x=> Q x+g i) i)=fderiv ℝ Q i:= by simp
       have he' : g=(fun x=> Q x+g i):=(hS i hi).symm; exact (congr_arg (fun f:E→ℝ=> fderiv ℝ f i) he').trans hp
     rwa [he]
  have hz': ‖g z‖ ≤ 1 := by
    have h: ‖g z-g 0‖ ≤ K₀*‖z-0‖:= (convex_closedBall _ _).norm_image_sub_le_of_norm_fderiv_le (fun x hx=> (hb _ hx).smooth.differentiableAt (by exact_mod_cast (show j ≠ 0 by omega))) hx h₀ he
    rw [show g 0=0 from zero_pr _,sub_zero,sub_zero] at h; exact le_trans h ((mul_le_mul_of_nonneg_left hZ (hy z he|>.2.nonneg)).trans hv)
  refine ⟨(((hb z he).climb (add_le_add_right hz' (K₀)) le_rfl |>.pine (hP (g z) ?_)).trim).shimmy (Eventually.of_forall fun _=>Flux.quotation _), (hy z he).1⟩
  exact abs_le.mp hz'

set_option maxHeartbeats 650000 in
lemma newness (G:Gauge){P:Teller G}(L : Side)(D: Patch)(hd: D.Branches P.bind G){N p d : ℝ→ℝ}{η r q : ℝ}(h: Torch η r q)(j:ℕ)(h₁:1≤j)(hW: W<0)(hp:Rate G L W p)(hN:Rate G L 0 N)(hk:Rate G L 0 d)(hh:∀ᶠ x:ℝ in atTop,0≤p x) : ∃ V:ℝ→ℝ, Rate G L 0 V ∧ ∀ᶠ t in atTop,
   ∀ (c f:Side)(S:StepData c f)(T:Tube G S)(F:Forest S.ratio)(X: Coat T F)(I:Finset (Tubular f G)), X.x=t→S.patch=D→Works P L t S T → Allow X.blank.plate (along S) (tubularPrice G L) η r q →(I.card:ℝ)≤N t → ∀ y:Body (↥I), (∀ i, |y i|≤ |d t|) → ∀ x:ZipP G c f, ‖x‖≤p t→ Brush j (V t) 1 (pledgeΛ X I y) x ∧ (planeQ X I x).PosDef:=by
  obtain ⟨A,e,q',Z,W',hY,hy,hW',HR⟩:= lofty P L D hd j h₁ hW hp hh η r q h
  obtain ⟨C,hC,hL⟩:= Brush.neighborhood (k:=j) 1 (Real.contDiffAt_log.mpr (by norm_num))
  obtain ⟨J,hJ,hP⟩:= Brush.compact (f:=Real.exp) (k:=j) isCompact_Icc (fun i (_: i ∈ Set.Icc (-1:ℝ) 1)=> Real.contDiff_exp.contDiffAt)
  let m:= tubularPrice G L; let a:=payE e q' A m; let b:= retain e q' A
  let f₀ t:= facePrice j (radiusB t) m A a; let u t:= driftP j (W' t)
  let w:= payE b (A⁻¹/2) (1+a) m; let K t:=vogueQ j C (|d t|) (f₀ t) w (N t) (u t); let V t:= (j.factorial*J)*(1+(1+(K t+1))*1)^j
  have hk' : Rate G L 0 K:= vogueRate _ _ (hk.compare (v:=fun t=>|d t|) (Eventually.of_forall fun x=> (abs_abs _).le)) hN (polynomial G L j m A a) (hW'.mul_left j) j
  have hV':Rate G L 0 V := by simpa only [V,mul_one,zero_mul] using! ((((Rate.const 1).add ((Rate.const 1).add (hk'.add (Rate.const 1)))).pow j).mul_left (j.factorial*J))
  have ha : 0<A⁻¹/2:=half_pos (inv_pos.mpr (zero_lt_one.trans_le hY.hQ))
  refine ⟨V,hV',?_⟩
  filter_upwards [HR,((hY.physical G L (-1) m).mul_left a).below (by norm_num) _ ha,(hk'.mul hp).below (by linarith) 1 zero_lt_one] with t ht hs hv c f S T F X I hX he hP' hp hD y hz z hZ
  have hs: Window.distPay e q' A m (radiusB t) ≤ _ := (le_abs_self _).trans hs
  let E:= ZipP G c f; let U:=closedBall (0:E) (p t); let C':=planeQ X I
  have hy i (h:i∈U): (C' i).PosDef ∧ Brush j (K t) 1 (frack C' (fun _=>y) i) i:= by
    obtain ⟨ha,hA,h₁⟩:=ht c f S T he hP' F X hX hp i (mem_closedBall_zero_iff.mp h)
    have hl : X.B=radiusB t:=congr_arg _ hX
    have he:= Vine.admits (dry X i) ha I (show Window.distPay e q' A (tubularPrice G L) X.B ≤ A⁻¹/2 from hl.symm ▸ hs)
    have hp: (C' i).PosDef:=Control.definite he.symmetry he.ground he.down
    have hh:= pleasing  X I id ha (hA.tilt le_rfl le_rfl le_rfl hA.scale) -- edit
    have hm : Brush j (vogueQ j C (|d t|) _ w (Fintype.card (↥I)) _) 1 _ i:= frisks (x:=i) hL.self_of_nhds hh he hp (Ω:=fun _=> y) (fun i'=> (Brush.certified zero_le_one (y i')).climb (hz i') le_rfl) (abs_nonneg _)
    refine ⟨hp,hm.climb ?_ le_rfl⟩
    unfold K f₀; rw [← hl]; exact vogueC hL.self_of_nhds.nonneg (abs_nonneg _) (Nat.cast_nonneg _) (by rwa [Fintype.card_coe]) hh.basis hh.pos he.disc
  have hx : Brush j (V t) 1 (fun x=> lens₀ (C' x) y/lens₀ (C' 0) y) z ∧ (C' z).PosDef := by
    apply frameRise (Ω:=fun _=>y) h₁ hZ ((le_abs_self _).trans hv) hP hy
  exact hx
end YM.ConnectedActivityE6.Blaze.Vine
