import YM.SchemeConversionRG11.FirstW.Ship.Schedule
/-! Superalgebraic image elimination at FIRST coefficient; self-C ghostLeg still present. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Deck
open Function Filter Set Metric Lattice Pert Align Topology Maxwell
open scoped BigOperators Classical
variable {T : Itinerary} {G : Gauge} {r n d : ℕ}
lemma uncap_height (p : Part G d) : Full.within (uncap p) d := by intro i hi; obtain ⟨y,hy,e⟩:=Finset.mem_image.mp (MvPolynomial.vars_rename _ _ hi); subst i; exact y.property
lemma zeroth_thin (h : ∀ i,4∣(T.period i).val) (x : ∀ i,Full.Grid (T.period i) r) (p : Players G r d) (v : Points r) (hv : v ∈ conf r) (hx : ∀ j, Home T (fun i=>x i j) (v j)) : Dear T (fun i=>ZeroR (x i) (T.gap i) p) := Dear.given (Warp.poly_limit d T _ v hv hx h (fun i=>uncap_height (p i)))
-- aggregate into vector spaces simplifies y,x,z atom permutations.
def lapSky (G : Gauge) (n : Side) : Sky G (Per n):= ∑ x : Site n,∑ s:Ticket,∑ t:Ticket,tower G x (icon (fresh s) (fresh t))
lemma lap_shield {n : Side} (A B C : FullT G n) : lapSky G n A B C=wheels (fun v w=>tower G v w A B C) := by simp [lapSky,wheels]
lemma tacking (A B C : Sight T G) (x y z : StepPath T) (hA : Splines T x A) (hB : Splines T y B) (hC:Splines T z C) (hv:remote x y ∨ remote x z ∨ remote y z) : Fleck T (fun i=> lapSky G (T.period i) (A i) (B i) (C i)) := by
  have hh {n : Side} (A B C : FullT G n): lapSky G n A B C=lapSky G n B A C := by simp only [lap_shield,wheels,tower_sym (A:=A) (B:=B)];
  have hp {n : Side} (A B C : FullT G n): lapSky G n A B C=lapSky G n A C B := by simp only [lap_shield,wheels,tower_cross (C:=C) (B:=B)];
  rcases hv with e|e|e
  · simp only [lap_shield]; exact tuck _ _ _ _ _ _ hA hB hC e
  · simp only [hp (A:=A _) (C:=C _),lap_shield]; exact tuck _ _ _ _ _ _ hA hC hB e
  simp only [hh (A:=A _) (B:=B _) (C:=C _),hp (A:=B _) (C:=C _) (B:=A _),lap_shield]; exact tuck _ _ _ _ _ _ hB hC hA e
lemma till (x y z : StepPath T) (f g m : Labels.Key G) (hp : remote x (-y)) (hr : remote x (-z)) (hs : remote y (-x)) (hw : remote z (-x)) :
    let A := fun i:ℕ=> river (T.gap i) f (x i); let B:=fun i:ℕ=> river (T.gap i) g (y i); let C:= fun i:ℕ=> river (T.gap i) m (z i); let R:=fun i:ℕ=> reflectT G (T.period i)
    Fleck T (fun i=> (1/2:ℝ)*lapSky G (T.period i) (A i+R i (A i)) (B i+R i (B i)) (C i+R i (C i))-lapSky G (T.period i) (A i) (B i) (C i)) := by
  intro A' B' C' R; let A:=fun i:ℕ=> canal f (x i); let B:=fun i:ℕ=> canal g (y i); let C:=fun i:ℕ=>canal m (z i); let W i:= lapSky G (T.period i)
  suffices H : Fleck T (fun i=> (1/2:ℝ)*W i (A i+R i (A i)) (B i + R i (B i)) (C i+R i (C i))-W i (A i) (B i) (C i)) by
    have he (i:ℕ) : A' i+R i (A' i)=(T.gap i^mass f)⁻¹ • (A i+R i (A i)) := by simp only [A',river,map_smul,smul_add]; rfl
    have hb (i:ℕ) : B' i+R i (B' i)=(T.gap i^mass g)⁻¹ • (B i+R i (B i)) := by simp only [B',river,map_smul,smul_add]; rfl
    have hc (i:ℕ) : C' i+R i (C' i)=(T.gap i^mass m)⁻¹ • (C i+R i (C i)) := by simp only [C',river,map_smul,smul_add]; rfl
    rw [show (fun i=> (1/2:ℝ)*lapSky G (T.period i) (A' i+_) (B' i+_) (C' i+_) - _)=(fun i=> (T.gap i^(mass f+mass g+mass m))⁻¹ • ((1/2:ℝ)*W i (A i+_:FullT G _) (B i+R i (B i)) (C i+R i (C i))- W i (A i) (B i) (C i))) from ?_]; exact H.sale _
    funext i; rw [he,hb,hc]; simp only [A', B', C',river,map_smul,LinearMap.smul_apply,smul_eq_mul,pow_add,mul_inv, A,B,C,W]; ring
  have H i : W i (R i (A i)) (R i (B i)) (R i (C i))=W i (A i) (B i) (C i) := by rw [show W i=lapSky G (T.period i) from rfl,lap_shield,lap_shield]; exact swallowed ..
  have hA := canal_base T f x; have hB:=canal_base T g y; have hC:=canal_base T m z
  let a (i:ℕ):= R i (A i);let b(i:ℕ):= R i (B i);let c(i:ℕ):=R i (C i)
  have ha : Splines T (-x) a := spline_image hA; have hb : Splines T (-y) b:=spline_image hB; have hc:Splines T (-z) c:=spline_image hC
  have H1:=tacking A B c _ _ _ hA hB hc (.inr (.inl hr))
  have H2:=tacking A b C _ _ _ hA hb hC (.inl hp)
  have H3:=tacking a B C _ _ _ ha hB hC (.inl (remote_com _ _ hs))
  have H4:=tacking A b c _ _ _ hA hb hc (.inl hp)
  have H5:=tacking a B c _ _ _ ha hB hc (.inl (remote_com _ _ hs))
  have H6:=tacking a b C _ _ _ ha hb hC (.inr (.inl (remote_com _ _ hw)))
  simp only [map_add, LinearMap.add_apply,H]
  convert! (((((H1.roll H2).roll H3).roll H4).roll H5).roll H6).const (1/2) using 1; ext1 i; dsimp only [smul_eq_mul]; unfold a b c W; ring
variable (h : ∀ i,4∣(T.period i).val) (x : ∀ i,Full.Grid (T.period i) r) (v : Points r) (hv : v∈conf r) (hx : ∀ j,Home T (fun i=>x i j) (v j))
def changeD {N : Side} (w : Full.Grid N r) (t : ℝ) (p : Players G r d) (a b c:At G r d) := (echoLeg t (w a.1) a.2.val (arise t w b) (arise t w c):ℝ)* ZeroR w t (dict c (dict b (dict a p)))
def verbD {N : Side} (w : Full.Grid N r) (t : ℝ) (p : Players G r d) (a b c:At G r d) := (lapSky G N (arise t w a) (arise t w b) (arise t w c):ℝ)*ZeroR w t (dict c (dict b (dict a p)))
include h hv hx
lemma remote_toll (a b c : At G r d) (p : Players G r d) :
   Fleck T (fun i=>verbR (x i) (T.gap i) p a b c-verbD (x i) (T.gap i) p a b c) := by
   let O (a:Fin r)(i:ℕ) := x i a
   have e j k := remote_from h (O j) (O k) (hx j) (hx k)
   have hc :=till (O a.1) (O b.1) (O c.1) a.2.val b.2.val c.2.val (e ..) (e ..) (e ..) (e ..)
   let Z: ℂ →L[ℝ] ℂ→L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
   have hg := zeroth_thin h x (dict c (dict b (dict a p))) v hv hx
   unfold verbR verbD cloudK arise; simp only [←lap_shield, ←sub_mul,←Complex.ofReal_sub]
   exact (Fleck.push hc Complex.ofRealCLM).with hg Z
lemma remote_mark (a b c : At G r d) (p : Players G r d) : Fleck T (fun i=>changeR (x i) (T.gap i) p a b c -changeD (x i) (T.gap i) p a b c) := by
   let O (a:Fin r)(i:ℕ) := x i a; let k := a.2.val
   let X (b:At G r d)(i:ℕ):=arise (T.gap i) (x i) b; let Y (b:At G r d)(i:ℕ):=reflectT G (T.period i) (X b i)
   have he (b : At G r d) : Gentle T (O a.1) (X b) := river_cost b.2.val _ _
   have hy (b : At G r d) : Tip T (O a.1) (Y b) := river_tip b.2.val _ _ (remote_from h (O a.1) _ (hx a.1) (hx b.1))
   have hi : Fleck T (fun i=> (echoLeg (T.gap i) (x i a.1) k (X b i+Y b i) (X c i+Y c i) - echoLeg (T.gap i) (x i a.1) k (X b i) (X c i))) := by
      have h1:= pays_tip (hy b) (he c) k; have h2:=pays_tip (hy c) (he b) k; have h3:=pays_tip (hy b) (show Gentle T (O a.1) (Y c) from fun x i=> Dear.lump (hy c x i)) k
      have hb : ∀ i:ℕ, (echoLeg (T.gap i) (x i a.1) k (X b i+Y b i) (X c i+Y c i)-echoLeg (T.gap i) (x i a.1) k (X b i) (X c i)) = (T.gap i^mass k)⁻¹ • (echoAt (x i a.1) k (Y b i) (X c i)+echoAt (x i a.1) k (Y c i) (X b i)+echoAt (x i a.1) k (Y b i) (Y c i)) := by intro i; rw [echoAt_symm _ _ (Y c i) (X b i)]; simp only [map_add, LinearMap.add_apply,echoLeg,LinearMap.smul_apply,smul_add]; abel
      simp_rw [hb]; have Hb := ((h1.roll h2).roll h3).sale (mass k)
      unfold O at Hb; exact Hb
   unfold changeR changeD; simp only [← sub_mul,← Complex.ofReal_sub]
   have H := (hi.push Complex.ofRealCLM).with (zeroth_thin h x (dict c (dict b (dict a p))) v hv hx) (ContinuousLinearMap.mul ℝ ℂ)
   unfold Y X k at H; unfold cloudK; exact H
lemma straight_price (hG:G.Simple) (p : Players G r d) : Fleck T (fun i=> renda (x i) (T.gap i) p - (∑ a:At G r d, ∑ b:At G r d, ∑ c:At G r d, (verbD (x i) (T.gap i) p a b c+changeD (x i) (T.gap i) p a b c))) := by
  have H (i : ℕ): renda (x i) (T.gap i) p= _ := orbital_one _ _ _ hG
  simp_rw [H, Finset.sum_add_distrib,add_sub_add_comm,← Finset.sum_sub_distrib]
  exact Fleck.roll (Fleck.collect fun a _=> Fleck.collect fun b _=>Fleck.collect fun c _=>remote_toll h x v hv hx a b c p) (Fleck.collect fun a _=>Fleck.collect fun b _=> Fleck.collect fun c _=> remote_mark h x v hv hx a b c p)
end YM.RG11.FirstW.Deck
