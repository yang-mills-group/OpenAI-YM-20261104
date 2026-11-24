import YM.Frontier6.Exact.Snap

/-! Firm capture on either products or extended inputs, not using *any*
ad hoc contact coordinate beyond the fixed detector. Outputs only on collars.
Estimates here for dual bounds; later apply at pairs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6
open Spec Function Filter Set MeasureTheory VMulti
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S) {n e d:ℕ}

def Probe.tip (p:Probe S)(K:Final C F S)(f:Reader K):=f none p.length p.exterior p.letter
def spotlight (f:Reader K)(b:Bool)(p:Probe S)(g:Ortho):= ((p.flip K b).roll K g).tip K f

structure Illuminates (d:ℕ)(f:Reader K)(x:Palette K d):Prop where
  seats: ∀ (i:Fin (d+1))(p:(hand K i.val).list)(b:Bool)(g:Ortho), x i p b g= spotlight K f b p.val g

def observable (d:ℕ)(f:Reader K):Prop:= ∃ x, Illuminates K d f x
lemma Illuminates.equips {x y:Palette K d}{f:Reader K}(hx:Illuminates K d f x)(hy:Illuminates K d f y):x=y:=by
   refine funext fun i=> funext fun p=> funext fun b=> ContinuousMap.ext fun g=>?_; rw [hx.seats,hy.seats]
lemma Illuminates.lowers {x:Palette K d}{f:Reader K}(hx:Illuminates K d f x)(he:e≤d): Illuminates K e f (previous K he x):=
   ⟨fun i p b g=> hx.seats (Fin.castLE (Nat.succ_le_succ he) i) _ b g⟩
lemma observable_down {f:Reader K}(hx:observable K d f)(he:e≤d): observable K e f:=⟨_, (Exists.choose_spec hx).lowers K he⟩
def display (d:ℕ)(f:Reader K):Palette K d:= if h:observable K d f then Exists.choose h else 0
lemma display_on {x:Palette K d}{f:Reader K}(h: Illuminates K d f x): display K d f=x:= by
   unfold display; rw [dif_pos (show observable _ _ _ from ⟨x,h⟩)]; exact Illuminates.equips K (Exists.choose_spec (show observable K d f from ⟨x,h⟩)) h
lemma displayed {f:Reader K}(h:observable K d f): Illuminates K d f (display K d f):=by rw [display,dif_pos h]; exact Exists.choose_spec h
lemma display_down {f:Reader K}(h:observable K d f)(he:e≤d): previous K he (display K d f)=display K e f:= ((display_on K ((displayed K h).lowers K he))).symm
/-- Actual fixed detector projection on readings. Junk when some probe values
are undefined, judged by geometry separately. -/
def capture (d:ℕ)(f:Reader K): S.Field d:= detector K d (display K d f)
lemma capture_lower {f:Reader K}(h:observable K d f)(he:e≤d):projectBelow K he (capture K d f)=capture K e f:=by unfold capture; rw [projects_short, display_down K h]

variable {X:Type*}
variable (D:ℝ→ Set X)(f:X→ Reader K)(σ:ℝ)
variable (h:DualEstimate K D f σ)(hL:Org.Grill C F)
variable (hf:∀ x:X,∀ (N:ℕ)(y:Points N), VMulti S (fun v=> f x none N y v))
variable (ε:ℝ)(hε:0<ε)
include h hL hf hε
lemma orbit_balance (p:Probe S)(t:Hand K d): ∃ B:ℝ,0 ≤ B ∧ ∀ᶠ r:ℝ in 𝓝[>] 0, ∀ x∈ D r, ∀ g:Ortho,
  ‖(p.roll K g).tip K (f x)-(p.roll K g).form K none d (handPoint K (f x) d t)‖ ≤ B*r^((d:ℝ)+1-σ-ε):=by
  let y(g:Ortho):= Points.move g p.exterior
  let N:= p.length
  let v(i:Fin N):= (p.letter i).1; let W:= number S v
  let U(g:Ortho):ScaleVec S v:= flying K p g
  let V(x:X)(g:Ortho)(T:Fin N→ S.Tag):= f x none N (y g) T-reading K none 0 (y g) T d (handPoint K (f x) d t)
  have ht:IsCompact (y '' univ):=isCompact_univ.image (spinner _)
  choose A hA H using fun i:W=> h.hand_residue K D f σ hL t (choice i) (L:= y '' univ) ht (by rintro z ⟨p',hp,rfl⟩; exact (p.roll K p').clear) ε hε
  choose g _ hg using fun i:W=> isCompact_univ.exists_isMaxOn univ_nonempty (show ContinuousOn (fun g:Ortho=> ‖factor (U g) i‖) univ from ((factor_cont U (fly_cont K p) i).norm).continuousOn)
  let C'(i:W):= ‖factor (U (g i)) i‖; let b(i:W):= C' i * A i
  refine ⟨∑ i:W,b i,Finset.sum_nonneg (fun i _=>mul_nonneg (norm_nonneg _) (hA _)),?_⟩
  filter_upwards [eventually_all.mpr H] with r H x hx u
  change ‖V x u (paint S v (U u))‖ ≤ _
  rw [VMulti.factors (show VMulti S (V x u) from (hf x N (y u)).sub (reading_multi K none _ _ _)) _, Finset.sum_mul]
  apply (norm_sum_le ..).trans; refine Finset.sum_le_sum fun i _=> ?_
  rw [norm_mul,mul_assoc]; exact mul_le_mul (hg i (mem_univ _)) (H i x hx (y u) (mem_image_of_mem y (mem_univ u)) none) (norm_nonneg _) (norm_nonneg _)
lemma detector_balance (t:Hand K d):
   ∃ B:ℝ,0 ≤ B ∧ ∀ᶠ r:ℝ in 𝓝[>] 0,∀ x∈ D r, ∀ y:Palette K d, Illuminates K d (f x) y→
    ‖detector K d y-handPoint K (f x) d t‖ ≤ B*r^((d:ℝ)+1-σ-ε):=by
   choose B hB H using fun (i:Fin (d+1)) (p:(hand K i.val).list)(b:Bool)=> orbit_balance K D f σ h hL hf ε hε (p.val.flip K b) t
   obtain ⟨C',hC,hT⟩:= ((eventually_ge_atTop (0:ℝ)).and (eventually_all.mpr fun i=>eventually_all.mpr fun p=> eventually_all.mpr fun b=>eventually_ge_atTop (B i p b))).exists
   let T:= detector K d; let w(x):= handPoint K (f x) d t
   refine ⟨‖T‖*C',mul_nonneg (norm_nonneg T) hC,?_⟩
   filter_upwards [eventually_all.mpr fun i=> eventually_all.mpr fun p=> eventually_all.mpr (H i p),self_mem_nhdsWithin] with r H hr x hx y hy
   let q:= r^((d:ℝ)+1-σ-ε); have hq:0 ≤ q:=Real.rpow_nonneg (mem_Ioi.mp hr).le _
   have he: ‖y-reaches K d d (w x)‖ ≤ C'*q:=by
      refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC hq)).2 fun i=> (pi_norm_le_iff_of_nonneg (mul_nonneg hC hq)).2 fun p=> (pi_norm_le_iff_of_nonneg (mul_nonneg hC hq)).2 fun b=> (ContinuousMap.norm_le _ (mul_nonneg hC hq)).mpr (fun g=>?_)
      change ‖y i p b g-(reaches K d d (w x) i p b g)‖≤ _; rw [hy.seats,reaches_at]; exact (H i p b x hx g).trans (mul_le_mul_of_nonneg_right (hT i p b) hq)
   nth_rw 1 [← detector_field K (handPoint K (f x) d t)]; rw [← map_sub, mul_assoc]
   exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left he (norm_nonneg T))
lemma detector_grade (w:e≤d):
   ∃ B:ℝ,0 ≤ B ∧ ∀ᶠ r:ℝ in 𝓝[>] 0,∀ x∈ D r,observable K d (f x)→
     ‖weight K e (projectBelow K w (capture K d (f x)))‖ ≤ B*r^((e:ℝ)-σ-ε):=by
   let t:=hand K d
   obtain ⟨B,hB,H⟩:= detector_balance K D f σ h hL hf ε hε t
   obtain ⟨A,hA,hV⟩:= h.hand_grade K D f σ t w ε hε
   let Q:= weight K e ∘L projectBelow K w
   refine ⟨A+‖Q‖*B, add_nonneg hA (mul_nonneg (norm_nonneg Q) hB),?_⟩
   filter_upwards [self_mem_nhdsWithin,H,hV,mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (zero_lt_one))] with r hr hH hE hr' x hx hf
   let y:= capture K d (f x); let z:= handPoint K (f x) d t
   change ‖Q y‖≤_; rw [add_mul,mul_assoc]
   refine le_trans (norm_le_norm_add_norm_sub' (Q y) (Q z)) (add_le_add (hE x hx) ?_); rw [← map_sub]
   have he:r^((d:ℝ)+1-σ-ε) ≤ r^((e:ℝ)-σ-ε):=Real.rpow_le_rpow_of_exponent_ge (mem_Ioi.mp hr) hr' (by linarith only [Nat.cast_le (α:=ℝ).mpr w])
   exact (Q.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((hH x hx _ (displayed K hf)).trans (mul_le_mul_of_nonneg_left he hB)) (norm_nonneg Q))
lemma detector_residue (d:ℕ)(v:Fin n→ S.Tag){L:Set (Points n)}(hK:IsCompact L)(hc:∀ y∈L,Points.cons 0 y∈conf _):
   ∃ B:ℝ,0 ≤ B ∧ ∀ᶠ r:ℝ in 𝓝[>] 0,∀ x∈ D r,observable K d (f x)→∀ y∈L,∀ s:StateIndex K,
    ‖f x s n y v-reading K s 0 y v d (capture K d (f x))‖≤B*r^((d:ℝ)+1-σ-ε):=by
   let t:=hand K d; obtain ⟨A,hA,H⟩:= detector_balance K D f σ h hL hf ε hε t
   obtain ⟨B,hB,hX⟩:= h.hand_residue K D f σ hL t v hK hc ε hε
   let p:Points n→ Points (n+1):= Points.cons 0
   obtain ⟨a,ha,hp⟩:= gap_compact (hK.image (show Continuous p by unfold p Points.cons points; fun_prop)) (image_subset_iff.mpr (show L⊆ p ⁻¹' _ from fun y hy=>hc y hy))
   obtain ⟨Z,hZ,hV⟩:= reading_bounded K hL v a ha d
   refine ⟨B+Z*A,add_nonneg hB (mul_nonneg hZ hA),?_⟩
   filter_upwards [H,hX] with r h hr x hx ht y hy s
   let T:= reading K s 0 y v d; let z:= handPoint K (f x) d t; let q:= capture K d (f x); let f':= f x s n y v
   change ‖f'-T q‖≤_
   rw [show f'-T q=f'-T z-T (q-z) by rw [map_sub]; ring, add_mul,mul_assoc]
   exact (norm_sub_le ..).trans (add_le_add (hr x hx y hy s) ((T.le_opNorm _).trans (mul_le_mul (hV s 0 y (hp (p y) (mem_image_of_mem p hy))) (h x hx _ (displayed K ht)) (norm_nonneg _) hZ)))
end YM.Frontier6
