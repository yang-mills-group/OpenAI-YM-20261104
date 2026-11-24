import YM.MS.ScaleForest.SmoothSwoop
/-!
# Continuity under the graph operations, given local uniform costs

Will serve for all physical parameters *and* z during the IR and Laurent
arguments. Local cost property with an aperture; no countable growth order
shared by all derivatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle
open scoped Topology ContDiff
variable {G : Gauge} {I E F J D U : Type} [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F] [FiniteDimensional ℝ E]
   {a b : I→ℝ} {q:J→I} {X Y : I → Mob G}
   {K : Rip G}

omit [FiniteDimensional ℝ E] in
theorem price_veg_shift {f:I→ E→F} (h : veg 0 f a) (q:J→I) : veg 0 (fun i=> f (q i)) (fun i=>a (q i)) :=
   Arc.hike (fun i=>h.smooth (q i)) (fun j=> by
     obtain ⟨C,hC,k,hk⟩:= Arc.ride h j; exact ⟨C,hC,k,fun i p=> hk (q i) p⟩)

theorem price_shift (h : fell 0 a X) (q:J→I) : fell 0 (fun i=>a (q i)) (fun i=> X (q i)) := fun m E _ _ _ w=> price_veg_shift (h m E w) q
theorem pay_price (hp : fell 0 a X) {M : ℝ} (h : 0<M) (he : ∀ i, a i ≤ M*b i) : fell 0 b X := fun m E _ _ _ w=> (hp m E w).raise ⟨ M,h,0,fun i _ _=>by simpa only [pow_zero,mul_one] using he i⟩

variable [TopologicalSpace I] [TopologicalSpace J] [TopologicalSpace D]
   {V:I→ℝ} {Z:I→ℂ} (hx : fell 0 1 X)

def Sway (X:I→Mob G) := ∀ m l, Continuous (fun i=> X i m l)
-- predicate localization.
def Vicinity (X:I→Mob G): Prop:= ∀ x:I, ∃ S∈𝓝 x, fell 0 1 (S.restrict X)

variable (h : Sway X)
include h

theorem repaint (q:J→I) (hp : Continuous q) : Sway (fun i=> X (q i)) := fun m l=> (h m l).comp hp
omit h in
theorem localized (h : ∀ x:I,∃ S∈𝓝 x, Sway (S.restrict X)) : Sway X:= by intro m l; apply continuous_iff_continuousAt.mpr; intro i; obtain ⟨S,hS,hQ⟩:= h i; exact ((continuousOn_iff_continuous_restrict (f:=fun x=> X x m l)).mpr (hQ _ _) i (mem_of_mem_nhds hS)).continuousAt hS
omit h in
theorem track_vicinity (h : Vicinity X) (q : J→I) (hp:Continuous q) : Vicinity (fun i=> X (q i)) := by
   intro j; obtain ⟨S,hS,hP⟩:= h (q j)
   exact ⟨ q ⁻¹' S, (hp.tendsto _).eventually hS, price_shift hP (fun i:(q ⁻¹' S)=>(⟨q i,i.property⟩:S))⟩

theorem repaintPlow (hp:Vicinity X)(a:ℂ)(hw : Continuous V): Sway (fun i=> plow a (V i) (X i)):= by
   apply localized; intro i; obtain ⟨S,hS,hP⟩:= hp i; refine ⟨ S,hS,fun m l=>?_⟩
   let W(t:S):= V t; let L:= ray l
   have hT (x:S): plow a (W x) (X x.val) m l= amount (a+mass L) (W x)*fieldVal (X x.val m) L (exp (W x)):=by
      simpa only [L,hush,fieldVal,ray_sail,smul_eq_mul,mul_one] using s_p_vector (X x.val) (ray l) 1 (W x) a
   have hr:= hw.comp (X:=↥S) continuous_subtype_val; unfold Set.restrict; simp_rw [show ∀ p:S, plow a (V p) (X p) m l = _ from hT];
   apply Continuous.mul (show Continuous (fun p:S=>amount _ (W p)) from ((Differentiable.continuous (𝕜:=ℝ) (fun t=>(amountD _ t).differentiableAt)).comp hr))
   exact veg_cont (hP m ℝ L) (fun p=> (h m _).comp continuous_subtype_val) id (fun t:S=>exp (V t)) continuous_id (Real.continuous_exp.comp hr)

theorem weaveSway (he : Sway Y) : Sway (fun i=> weave (X i) (Y i)) := by
   intro m w; simp_rw [weave,scattered];
   have ht(w:Legs (Shore G m)) (V:I→ Shared (Shore G m) ℂ) (hu:∀ p q,Continuous (fun i=> V i p q)) : Continuous (fun i=> scatter (field Landau.parity) w (V i)):= by
      induction w generalizing V with | nil=> exact hu [] [] | cons i w ih=> exact ih _ fun p q=> (hu (i::p) q).add (continuous_const.mul (hu p (i::q)))
   exact ht w _ (fun l r=> (h m l).mul (he m r))

theorem Sway_smul (hv:Continuous Z): Sway (Z • X):= fun m l=> hv.mul (h m l)
theorem Sway_plus (he:Sway Y): Sway (X+Y):= fun m l=> (h m l).add (he m l)

omit h in
-- Continuity of mass scaling function (actual input maybe variable scales)
theorem tenor_ride (hv : Continuous V)(hz : Continuous Z)(ht : ∀ i, Z i∈Town): Continuous (fun i=> tenorK (Z i) (V i)) := by
   simp_rw [restore_tape]; apply Continuous.mul _ (by fun_prop)
   exact continuous_iff_continuousAt.mpr fun i=> (fee_H _ (ht i)).continuousAt.comp (hz.continuousAt (x:=i))
variable (he : Knot false K)
include hx he
theorem swayPastCont [FirstCountableTopology I] (hX : ∀ i, Sturdy false (X i))
    {N:ℕ} (hz:Continuous Z) (hw : ∀ i, Z i∈Town) (ht : ∀ i, ‖Z i‖ ≤ (N:ℝ)) : Sway (fun i=> ocean (Z i) K (X i)):= by
   have hp (n:ℕ) : scaleC 0 1 (fun i=>‖2*(Z i-n)‖) := by
       refine ⟨1+2*((N:ℝ)+n),by positivity,0,fun i _ _=>?_ ⟩; obtain hh:= norm_sub_le (Z i) (n:ℂ); simp at hh ⊢; linarith [ht i]
   have hT (i:I) : 2*(Z i).re+1≤ ((2*N+1:ℕ):ℝ):= by push_cast; linarith [ht i, Complex.re_le_norm (Z i)]
   intro m l; let f(i:I):= wing (Z i) K (X i) (ray l)
   have hf : quiet 0 f 1:= by convert! sky hp hx (transport he.price) (fun _=> zero_le_one) (ray l) using 1; ext; simp
   have hg : hush f:= by
      intro x; unfold f wing Wtr; simp_rw [Pi.add_apply, Pi.smul_apply, at_trc]; refine Continuous.add ?_ ((continuous_const.mul (hz.sub continuous_const)).smul ?_)
      · exact continuous_finsetSum _ (fun i _=> continuous_finsetSum _ (fun j _=>Continuous.mul continuous_const (h _ _)))
      simp_rw [yeast]; exact continuous_finsetSum _ fun i _=> continuous_finsetSum _ fun j _=> continuous_finsetSum _ fun k _=> continuous_finsetSum _ fun u _=> continuous_const.mul (h _ _)
   exact swoopH (Px m) hz hw hT hf hg (fun i=> wing_mirror (hX i) he.token _ _) m (1:ℝ)

omit hx
include he

theorem swayOcean [FirstCountableTopology I] (hy : Vicinity X) (hX : ∀ i, Sturdy false (X i))
    {N : ℕ} (hz : Continuous Z) (hw : ∀ i, Z i∈Town) (ht : ∀ i, ‖Z i‖ ≤ (N:ℝ)) : Sway (fun i=> ocean (Z i) K (X i)):= by
   apply localized; intro x; obtain ⟨S,hS,hT⟩:= hy x
   exact ⟨ S,hS,swayPastCont hT (repaint h (Subtype.val (p:=fun i=>i∈S)) continuous_subtype_val) he (fun i=> hX i.val) (hz.comp continuous_subtype_val) (fun i=> hw i.val) (fun i=> ht i.val)⟩

omit h he [TopologicalSpace I] in
theorem vic_con {S R : Set I} (hS : fell 0 1 (S.restrict X)) (he : R⊆ S): fell 0 1 (R.restrict X):=
   price_shift hS (fun x:R=>(⟨(x:I),he x.property⟩:S))

omit h he in
theorem weave_vic (h : Vicinity X) (he : Vicinity Y) : Vicinity (fun i=> weave (X i) (Y i)):= by
   intro x; obtain ⟨S,hS,hP⟩:= h x; obtain ⟨V,hV,hU⟩:= he x; refine ⟨ S∩V, inter_mem hS hV,?_ ⟩
   convert! weave_price (vic_con hP (inter_subset_left (t:=V))) (vic_con hU (inter_subset_right (s:=S))) using 1; simp

omit h he in
theorem rephase_vic {A:I→QP} (hp : Vicinity X) (ht : Continuous A) : Vicinity (fun i=> rephase (A i) (X i)):= by
   intro x; obtain ⟨S,hS,hP⟩:= hp x; let C:=1+‖A x‖; have hc : C>0:= by unfold C; positivity
   let T : Set I:= {y| ‖A y‖ < C}; have hT : T ∈𝓝 x:=  by
     exact (ht.norm.tendsto x).eventually (gt_mem_nhds (b:=‖A x‖) (a:=C) (by simp [C]))
   have hu : (E: Type)→ [inst1:NormedAddCommGroup E]→ [inst2:NormedSpace ℝ E]→ (Arc.path (0:UScale (S∩T:Set I))).full.Le (fun i (_:E)=>‖A i‖) (fun _ _=>1) := fun E _ _=> ⟨ C,hc,0,fun i u _=> by rw [pow_zero,mul_one,mul_one]; exact le_of_lt (show _ < C from i.property.2)⟩
   exact ⟨ S∩T, inter_mem hS hT, rephase_price (P:=fun i:(S∩T:Set I)=> A i.val) (vic_con hP (inter_subset_left (t:=T))) hu⟩

omit he in
theorem rephase_sway {A:I→QP}(ht:Continuous A) : Sway (fun i=> rephase (A i) (X i)):= by
   intro m l; refine Continuous.mul ?_ (h m l); simp_rw [ waveFact,Tone.rights (A _ ) ]; exact ((bill_sm (onPlane m (net l))).continuous).comp ht

variable [FirstCountableTopology I] (hc : Vicinity X) (hX : ∀ i, Sturdy false (X i)) {N : ℕ} (hz : Continuous Z) (hw : ∀ i, Z i∈Town) (ht : ∀ i, ‖Z i‖ ≤ (N:ℝ))
include hc hX hz hw ht

theorem swayClose (hV : Continuous V) : Sway (fun i=> closeG K (Z i) (V i) (X i)):= by simp_rw [closeG_eq]; exact Sway_smul (swayOcean h he hc hX hz hw ht) (tenor_ride hV hz hw)
theorem swayPinned (hV : Continuous V) {A:I→QP} (hA : Continuous A)
    (hY : Sway Y) (hy : Vicinity Y) (hr : ∀ i, Sturdy false (Y i)) (hv : reverseF K) (hb : closedF K false) : Sway (fun i=> pinned K (Z i) (V i) (A i) (X i) (Y i)) := by
   have hcT (f:I→Mob G) (hp:Vicinity f) (i:I) : kPrice (f i):= by obtain ⟨S,hS,hL⟩:= hp i; exact Rock.fee hL (⟨i,mem_of_mem_nhds hS⟩:S)
   simp_rw [placedEq he hb hv ⟨hcT _ hc _,hX _⟩ ⟨hcT _ hy _,hr _⟩ (hw _)];
   apply Sway_smul (Z:=fun i=>tenorK (Z i) (V i)) (?_) (tenor_ride hV hz hw)
   have h_U:= rephase_sway h hA; have h_u:= rephase_vic hc hA; have h_W i:= rephase_token (A i) (hX i)
   obtain ht_x:= swayOcean h_U he h_u h_W hz hw ht; obtain h_ty:= swayOcean hY he hy hr hz hw ht
   intro m w; exact (((swayOcean (weaveSway h_U hY) he (weave_vic h_u hy) (fun i=> weave_token (h_W i) (hr i)) hz hw ht) m w).sub ((weaveSway ht_x hY) m w)).sub ((weaveSway h_U h_ty) m w)

omit hx hX he hc hz hw ht [FirstCountableTopology I] in
theorem swayBridge (hY : Sway Y) (K : Rip G) : Sway (fun i=> bridgeG K (X i) (Y i)) := by
   intro m w; let p:= field (Landau.parity (A:=Arts.L m) (C:=G.ColorIndex)) (P:=SectorP m)
   have ht (w:Legs (Shore G m))(f:I→Shared (Shore G m) ℂ)(h:∀ l r,Continuous (fun i=> f i l r)):
      Continuous (fun i=> scatter p w (f i)):= by
     induction w generalizing f with | nil=> exact h [] [] | cons i w ih=> exact ih _ fun l r=> (h (i::l) r).add (continuous_const.mul (h l (i::r)))
   unfold bridgeG; dsimp only; exact ht w _ (fun l r=> continuous_finsetSum _ (fun i _=> continuous_finsetSum _ (fun j _=> (continuous_const.mul (continuous_const.mul (h m _))).mul (hY m _))))
end YM.MS.ScaleForest
