import YM.XSpace.Compat.Ride
import YM.XSpace.ScorePad

/-! # Convergence of harmonic playback extraction on convergent external data -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Scale
open YM.XSpace.Compat.KP
open Lattice Sail Litter Maxwell Analysis Tensor Further.FreeCovariance.KP Function Filter Set Asymptotics
open scoped Topology BigOperators ContDiff
variable {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]{d n:ℕ}

-- at the root, evaluating just for clarity. actual horizon values feed exact stencil interpolation
abbrev Radio (F:Type*) := Axis→E4→F
def Tuned (X:Radio F): Prop:=∀ i,ContDiffAt ℝ ∞ (X i) 0
def music (d:ℕ)(X:Radio F)(h:Tuned X):Folder d F:=fun i j=>⟨Tensor.coeff (X j) i.val 0, coeff_symm ((h j).of_le (WithTop.coe_le_coe.mpr le_top))⟩
lemma rode (t:Fin n→Axis){x:E4}{f:E4→F}(h:ContDiffAt ℝ ∞ f x): ride (List.ofFn t) f x=(n.factorial:ℝ) • Tensor.coeff f n x (basis∘t):=by
  induction n generalizing f with
  | zero=> simp [ride,Tensor.coeff_apply_zero]
  | succ n ih=>
    let i:=t 0; let s:=Fin.tail t; rw [List.ofFn_succ,ride,show basis ∘ t=Fin.cons (basis i) (basis ∘ s) from funext fun j=>by cases j using Fin.cases <;> rfl,Tensor.coeff_apply_cons (h.of_le (WithTop.coe_le_coe.mpr le_top))]; change ride (List.ofFn s) _ _=_; rw [ih s (grad_smooth _ h (by simp)),smul_smul,Nat.factorial_succ,Nat.cast_mul]; field_simp; rfl

variable {ι:Type*}{L:Filter ι}{a:ι→ℝ}{r:ι→ℕ}
private lemma likely {V:ι→Stamp n F}{w:Stamp n F}(h: ∀ t:Fin n→Axis,Tendsto (fun i=> (V i).val (basis∘t)) L (𝓝 (w.val (basis ∘ t)))):Tendsto V L (𝓝 w):=by
  let U:Stamp n F→ₗ[ℝ] ((Fin n→Axis)→F):= LinearMap.pi fun i => (ContinuousMultilinearMap.apply ℝ _ F (basis∘i)).toLinearMap ∘ₗ (stamps F n).subtype
  obtain ⟨Q,H⟩:= U.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (show Injective U from fun x y h=>Subtype.ext (piece_ext fun i=>congr_fun h i)))
  have he:= Q.continuous_of_finiteDimensional.continuousAt.tendsto.comp (show Tendsto (fun i=> U (V i)) L (𝓝 (U w)) from tendsto_pi_nhds.mpr h)
  rw [show Q (U w)=w from LinearMap.congr_fun H _] at he; exact he.congr fun i=> LinearMap.congr_fun H _

def AtRoots (L:Filter ι)(a:ι→ℝ)(A:ι→Tape F)(X:Radio F):Prop:= ∀ (l:List Axis)(j:Axis), Tendsto (fun i=> (a i)⁻¹^(1+l.length) • crack l (twig j (A i)) 0) L (𝓝 (ride l (X j) 0))
variable {A:ι→Tape F} {X:Radio F} (h:AtRoots L a A X) (hx:Tuned X) (S:Tendsto a L (𝓝 0))(he:∀ᶠ i in L,0<a i)
include h hx S he
lemma kind (d:ℕ): Tendsto (fun i=>meter d (a i)⁻¹ (extract d (A i))) L (𝓝 (music d X hx)):=by
  have ht (j:Axis): Tendsto (fun i=> packets d j (meter d (a i)⁻¹ (extract d (A i)))) L (𝓝 (packets d j (music d X hx))):= by
    simp_rw [amounted,pack]; apply high (half j) 1 _ _ S (he.mono fun i hi=> ne_of_gt hi); apply tendsto_pi_nhds.mpr; intro i; apply likely; intro t; specialize h (List.ofFn t) j; rw [rode t (hx j)] at h; let b:ℝ:=(i.val.factorial:ℝ)
    have hp:= (show Tendsto (fun _:ι=>b⁻¹) L (𝓝 b⁻¹) from tendsto_const_nhds).smul h; rw [show ∀ y:F, b⁻¹ • ((i.val.factorial:ℝ)) • y=y from fun y=> inv_smul_smul₀ (by unfold b; positivity) _] at hp
    exact hp.congr fun l=>by change b⁻¹ • _= (a l)⁻¹^(1+i.val) • (talent i.val (twig j (A l))).val _; rw [talent_ap, List.length_ofFn,smul_comm b⁻¹,peaked]
  apply tendsto_pi_nhds.mpr; intro i; exact tendsto_pi_nhds.mpr fun j=> tendsto_pi_nhds.mp (ht j) i
lemma harmonizes (d:ℕ): Tendsto (fun i=> orchestra d (a i)⁻¹ (gather d (A i))) L (𝓝 (collect (music d X hx))):= by simp_rw [gather,LinearMap.comp_apply,← projected]; exact (LinearMap.continuous_of_finiteDimensional (𝕜:=ℝ) (E:=Folder d F) (F':=Organ d F) collect).continuousAt.tendsto.comp (kind h hx S he _)
theorem identical [NeBot L] (K:Studio L a r A)(d:ℕ): rawPack (collect (music d X hx))=music d X hx:=by
  have ht: Tendsto (fun i=> rawPack (orchestra d (a i)⁻¹ (gather d (A i)))) L (𝓝 (rawPack (collect (music d X hx)))):=tendsto_pi_nhds.mpr fun i=>
    continuous_subtype_val.continuousAt.tendsto.comp (tendsto_pi_nhds.mp (harmonizes h hx S he d) i)
  symm; apply sub_eq_zero.mp; apply tendsto_nhds_unique ((kind h hx S he d).sub ht)
  apply tendsto_pi_nhds.mpr; intro j
  have he₀:= K.bill (he.mono fun i hi=>le_of_lt hi) d; have hp:= IsBigO.smul (isBigO_refl (fun i=>(a i)⁻¹^(1+j.val)) L) (isBigO_pi.mp he₀ j)
  have hY:=hp.trans_tendsto (by
    let k:= d+2-(1+j.val); have hk:0<k:=by unfold k; have :=j.isLt; omega
    have hv:= S.pow k; rw [zero_pow (Nat.ne_of_gt hk)] at hv; refine hv.congr' ?_
    filter_upwards [he] with i hi; change a i^k=(a i)⁻¹^_ * a i^_; rw [show d+2=1+j.val+k by unfold k at *; have ht:=j.isLt; omega,pow_add _ (1+j.val),← mul_assoc,← mul_pow, inv_mul_cancel₀ hi.ne',one_pow,one_mul])
  exact hY.congr (fun i=> smul_sub _ _ _)

-- normalized high mode fee for motif playback at any translated point
omit h hx in
lemma tendency (l:List Axis) (p:ι→Cover)(v:E4)(u:ι→Stamp d F)(x:E4)(A:Stamp d F) (ht:Tendsto u L (𝓝 A))(H:Tendsto (fun i=> a i • rcast (p i)) L (𝓝 x)): Tendsto (fun i=> (a i)⁻¹^l.length • crack l (feed v ((a i)^d • u i)) (p i)) L (𝓝 (ride l (motifValue A) x)):=by
  induction l generalizing v d with
  | nil=>
    have he': Tendsto (fun i=>(a i) • (rcast (p i)+v)) L (𝓝 x):=by simp_rw [smul_add]; simpa using H.add (S.smul (show Tendsto (fun _:ι=>v) L (𝓝 v) from tendsto_const_nhds))
    have hy:=slopes (tendsto_subtype_rng.mp ht) he' S; exact hy.congr fun i=>by rw [map_smul]; simp only [crack,List.length_nil,pow_zero,one_smul];rfl
  | cons i l ih=>
    let z:=v+half i
    cases d with
    | zero=>
      rw [ride,show grad i (motifValue A)=0 from funext (plane i A),ride_nil]
      refine (tendsto_const_nhds (x:=(0:F)) (f:=L)).congr' ?_
      filter_upwards with i'; change 0= _ • crack _ _ _; rw [snack,feed_const,← peaked,map_zero];simp
    | succ d=>
      have ht:= ih z _ (A:=dip i A) ((dip i (n:=d) (F:=F)).continuous_of_finiteDimensional.continuousAt.tendsto.comp ht)
      rw [ride,funext (climbs A i)]; refine ht.congr' ?_
      filter_upwards [he] with k hk
      set b:=a k; change b⁻¹^l.length • _=_; rw [snack,funext fun x=>feed_one x i v ((a k)^(d+1) • u k)]
      simp_rw [← peaked,map_smul,List.length_cons,pow_succ,Pi.smul_apply,smul_smul]; dsimp only [comp_apply]; rw [show a k=b from rfl]; congr 1; field_simp
end YM.XSpace.Scale
