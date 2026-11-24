import YM.Next.STATIONARY.Films.LeadingRay
import YM.AllOrder.Haiku.Deduce
set_option autoImplicit false
noncomputable section
/-!
# Retreat at exact winding-free branch, linear Ward and TWO-leg lift

Adapted (Lean proof below) from Lift.Ward & Films.LeadingRay to the LINEAR
Ward regime on the *order-k output*. Includes [shared labels]. Do NOT
premise invariance of a homogeneous WRONG potential under nonlinear Gauge.
-/
namespace YM.Stationary.Haiku
open Function Lattice RG Exterior Wilson Precision Bloch Laurent Filter Finset
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius
variable {G : Gauge} {n t : ℕ} {m : Side}
def tolerant (F:Link G m→ℝ):=∀ x:Swatch G m,F (x.2-gradientA G m x.1)= F x.2
variable (F:Link G m→ℝ)
lemma agrees (x:Fin n→Swatch G m) (h:tolerant F)(hp:AnalyticAt ℝ F 0):
    iteratedFDeriv ℝ n F 0 (fun i => (x i).2-gradientA G m (x i).1)=iteratedFDeriv ℝ n F 0 fun i => (x i).2 := by
 let B:= ContinuousLinearMap.snd ℝ (BaseSites G m) (Link G m); let A:= B- (gradientA G m).toContinuousLinearMap ∘L ContinuousLinearMap.fst ℝ (BaseSites G m) (Link G m)
 have he:F ∘ A=F∘B:= funext h; have hv (v:Swatch G m →L[ℝ] Link G m): iteratedFDeriv ℝ n (F ∘ v) 0 x=iteratedFDeriv ℝ n F 0 (v ∘ x):=by rw [wired v (by rw [map_zero]; exact hp), map_zero]
 exact ((hv A).symm.trans ((congr_arg (fun f:Swatch G m→ℝ=> iteratedFDeriv ℝ n f 0 x) he).trans (hv B)))

lemma agreeC (x : Fin n → Phase (Lines G m 1)) (y : Fin n → Phase (Lines G m 0))
    (h : tolerant F) (hp : AnalyticAt ℝ F 0) :
    noteAt F n (fun i => x i-gradientA G m (y i))=noteAt F n x := by
  classical
  let K := Lines G m 1 ⊕ Lines G m 0
  let D : Phase K →ₗ[ℂ] Phase (Lines G m 1) := LinearMap.pi fun i => LinearMap.proj (Sum.inl i)
  let Y : Phase K →ₗ[ℂ] Phase (Lines G m 0) := LinearMap.pi fun i => LinearMap.proj (Sum.inr i)
  have he : (noteAt F n).compLinearMap (fun _ => D-gradientA G m ∘ₗ Y)=(noteAt F n).compLinearMap fun _ => D := by
    apply enlarge_unique; intro b
    let p (j : Fin n) : Swatch G m := (fun i => b j (Sum.inr i),fun i => b j (Sum.inl i))
    simp only [MultilinearMap.compLinearMap_apply, Function.comp_apply,LinearMap.sub_apply,LinearMap.comp_apply]
    rw [show (fun a => D (axes _) - _) = axes ∘ (fun i : Fin n => (p i).2-gradientA G m (p i).1) by
      funext i j; simp [gradientA,D,Y,p,axes],
      show (fun a : Fin n => D (axes (b a))) = axes ∘ (fun i => (p i).2) from rfl,
      note_real,note_real,Tensor.coeff,_root_.smul_apply,_root_.smul_apply,agrees F p h hp]
  exact DFunLike.congr_fun he (fun i => Sum.elim (x i) (y i))

lemma note_blank (x : Fin n → Phase (Lines G m 1)) (y : Phase (Lines G m 0)) (i : Fin n)
    (h : tolerant F) (hp : AnalyticAt ℝ F 0) : noteAt F n (update x i (gradientA G m y))=0 := by
  have he := agreeC F (update x i 0) (Pi.single i (-y)) h hp
  rw [show (fun a => update x i 0 a - gradientA G m ((Pi.single i (-y) : Fin n → Phase (Lines G m 0)) a))=update x i (gradientA G m y) from funext fun j => by
    by_cases h : j=i <;> simp [h], (noteAt F n).map_coord_zero (m:=update x i 0) i (by rw [update_self])] at he
  exact he

lemma contract (x : Fin (t+1) → Site m) (hx : ∑ i,x i=0)
    (w : Ink G (t+1)) (i : Run (t+1)) (j : Fin (t+1))
    (h : tolerant F) (hp : AnalyticAt ℝ F 0) :
    ∑ k : TypeFace 1, symbol 0 (plotted (outphase x) j) k vac * noteAt F _ (glyph x w (update i j k))=0 := by
  have he := note_blank F (glyph x w i) (relay (x j) (vac,w j)) j h hp
  rw [gradient_wave] at he
  rw [MultilinearMap.map_update_sum] at he
  rw [waved_symbol x hx]; apply Eq.trans _ he
  refine sum_congr rfl fun k _ => ?_
  have hu : glyph x w (update i j k)=update (glyph x w i) j (relay (x j) (k,w j)) := funext fun l => by by_cases h : l=j <;> simp [h,glyph]
  rw [hu]; simp
section service
variable {m : ℕ → Side} {η A : ℝ} {ε : ℕ → ℝ} {F : ∀ i, Link G (m i) → ℝ} {f : Picture G t}
private lemma plot_cont (a : Fin (t+1)) : Continuous (fun p : Space t => plotted p a) := by
  refine Fin.cases ?_ (fun a => ?_) a <;> simp only [plotted,Fin.cons_zero,Fin.cons_succ]
  · apply continuous_pi; intro k; simp only [missing,Pi.neg_apply,Finset.sum_apply,Function.comp_apply]; fun_prop
  exact continuous_pi fun i => continuous_apply _


/-- Transfers of all output lift conditions except ray vanishing orders.
Uniformity from `Recorded`. `Quiets` does not require equality of constants. -/
theorem purchased_At (hν : Tendsto (fun i => (m i).val) atTop atTop)
    (hd : Tendsto ε atTop (𝓝 0)) (h : ∀ i j, Firm η A (f i j)) (hp : ∀ p, Recorded f (F p) (cents (m p)*ε p))
    (he : ∀ p, AnalyticAt ℝ (F p) 0) (ha : ∀ p, Stained G (F p)) (hs : ∀ p, tolerant (F p))
     : Features f η A := by
  constructor; exact h
  · intro x r i b
    obtain ⟨p,u,H,U⟩ := fleet m hν (axes r) (axes_real r)
    have hg (v : TypeFace 1) : Tendsto
        (fun y => symbol 0 (plotted (u y) i) v vac * standing m F p x (update b i v) y)
        atTop (𝓝 (symbol 0 (plotted (axes r) i) v vac * f x (update b i v) (axes r))) := by
      apply Tendsto.mul _ (harvest h hp hd r p u H U _ _)
      have ht : Continuous (fun z : Momentum => symbol 0 z v vac) := by simp only [symbol, Exterior.q,wedge,Matrix.sum_apply,Matrix.smul_apply]; fun_prop
      exact ((ht.comp (plot_cont i)).continuousAt.tendsto.comp H)
    have hv := tendsto_finsetSum univ fun v _ => hg v
    refine tendsto_nhds_unique hv (?_)
    have hy (i' : ℕ) := contract (F i') (p i') (U i').1 x b i (hs i') (he i')
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun i' => ?_)
    symm
    simp_rw [← rolls_symbol (projections_roll (U i').2 i)]
    unfold standing; simp_rw [mul_left_comm _ (cents (m i'):ℂ)⁻¹]; rw [← Finset.mul_sum,hy i',mul_zero]
  · intro x i a hb
    let r : Corn _ := fun j => (a j).re; have hr : a=axes r := (axes_of_real hb).symm
    obtain ⟨p,u,H,U⟩ := fleet m hν (axes r) (axes_real r)
    have hy := harvest h hp hd r p u H U x i
    have hh : ∀ j, ∑ k,(-p j) k=0 ∧ rolls (outphase (-p j)) (-u j) := by
      intro j; refine ⟨?_,(reflection_negative _).trans (U j).2.neg⟩
      simp only [Pi.neg_apply,sum_neg_distrib,(U j).1,neg_zero]
    have hz := harvest h hp hd (-r) (fun i => -p i) (fun i => -u i) (axes_flip r |>.symm ▸ H.neg) hh x i
    have ht := hz.star
    rw [hr]; rw [axes_flip] at ht
    refine tendsto_nhds_unique (?_ : Tendsto (standing m F p x i) atTop _) hy
    convert ht using 1; ext1 z
    simp only [standing,star_mul,glyph_flips,← note_fixed]; simp [mul_comm]
  intro r i
  obtain ⟨p,u,H,U⟩ := fleet m hν (axes r) (axes_real r)
  have hv j : fixedInks G (fun x => standing m F p x i j) := by
    have hw := film_proof (p j) i (he j) (ha j)
    let k := (cents (m j))⁻¹
    have hI : (cents (m j):ℂ)⁻¹=(k:ℂ) := by simp [k]
    unfold standing
    rw [hI]; constructor
    · simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using!
        (paints G _).smul_mem k hw.1
    simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using!
        (paints G _).smul_mem k hw.2
  have hy x := harvest h hp hd r p u H U x i
  have hx := (paints G (t+1)).closed_of_finiteDimensional
  refine ⟨hx.mem_of_tendsto (b:=atTop (α:=ℕ)) (tendsto_pi_nhds.mpr (fun x => ?_)) (Eventually.of_forall (fun j => (hv j).1)),
    hx.mem_of_tendsto (b:=atTop (α:=ℕ)) (tendsto_pi_nhds.mpr (fun x => ?_)) (Eventually.of_forall (fun j => (hv j).2))⟩
  exact Complex.continuous_re.continuousAt.tendsto.comp (hy x)
  exact Complex.continuous_im.continuousAt.tendsto.comp (hy x)
end service

variable {f : Picture G 1} {adm:Signed→Prop} {σ A:ℝ}
lemma charter {m : ℕ→ Side} {F : ∀ i, Link G (m i) → ℝ} {ε : ℕ→ℝ} (hm : Tendsto (fun i => (m i).val) atTop atTop)
    (he : ∀ i j,Firm σ A (f i j)) (hd : Tendsto ε atTop (𝓝 0)) (hf : ∀ i, Recorded f (F i) (cents (m i)*ε i))
    (hA : ∀ i, AnalyticAt ℝ (F i) 0) (hV : ∀ i, tolerant (F i)) (hp : ∀ i, Stained G (F i)) (hW : ∀ p, ∀ s : Signed, adm s → F p ∘ orderTurn (G:=G) (m:=m p) s=ᶠ[𝓝 0] F p) : TributeColor f σ A adm := {
    toFeatures := purchased_At hm hd he hf hA hp hV
    perm := fun p u v a b => by unfold pressLens; rw [map_neg]; exact cross_stage he hf hm hd hA ..
    law := fun p i a s hs => turn_stage he hf hm hd s hA (fun i => hW i s hs) p i a }
lemma multiLens (h:TributeColor f σ A Unsigned) (u i) : Rays 2 (f u i ∘ axes) := by
 obtain ⟨a,ha⟩:= axisEquiv.surjective (i 0); obtain ⟨b,hb⟩:= axisEquiv.surjective (i 1)
 have hz : i=![coord a,coord b]:= funext fun k=> Fin.cases ha.symm (fun k=>by fin_cases k; exact hb.symm) k
 rw [hz]; let hv:= h.crop_edict (fun _ h=>h) u a b; intro p
 obtain ⟨p,rfl⟩:= roads.surjective p; let ht := hv p; simpa only [pressLens,map_smul] using! ht
end YM.Stationary.Haiku
end
