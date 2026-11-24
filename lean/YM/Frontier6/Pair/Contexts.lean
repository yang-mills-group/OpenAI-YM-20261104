import YM.Frontier6.Pair.Folio
import YM.Frontier6.Pair.Packing

/-! Exterior contexts for a horizontal capture. Keep any fixed number of
external probes, allowing all *continuum* ties not actually coincident, with
constants on +margin. Product inputs of this capture still require grid/stage
geometry. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Platform
open Function Filter Set Lattice Wilson RG Source MergeProof MergeProof.Ribbons Next.UVStress
open MeasureTheory Measure Analysis
open Bid Spec Extraction Cells Around OS Word MeasureTheory
open scoped Topology InnerProductSpace BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Extraction.Order} {f:Filter (ℕ×ℕ)}
variable {j k m b l n D d t : ℕ} (B:C.label d) (U:C.label t)

private lemma plane_price (i : Fin n)(a:Axis)(y:ℝ): volume {x:Points n| x i a=y}=0:=by
    let f : Points n →ₗ[ℝ] ℝ := ((EuclideanSpace.proj a).toLinearMap).comp (PiLp.projₗ (𝕜:=ℝ) 2 (fun _=>E4) i)
    let X (y:ℝ):= points (n:=n) (Pi.single i (y • basis a))
    have he(x:Points n): x i a=f x:=rfl
    have ht(y): f (X y)=y:=by rw [← he]; simp [X]
    let M:= AffineSubspace.mk' (X y) (LinearMap.ker f); have h(x:Points n): x∈M ↔ x i a=y:=by rw [he,AffineSubspace.mem_mk',vsub_eq_sub,LinearMap.mem_ker,map_sub,ht,sub_eq_zero]
    rw [show {x:Points n | x i a=y}= M from Set.ext fun i=>(h i).symm]; apply Measure.addHaar_affineSubspace; intro hp
    have hh := (h (X (y+1))).mp (hp.symm ▸ AffineSubspace.mem_top _ _ _); rw [he,ht] at hh; linarith
private lemma piece_generic (x:E4)(y:Points n)(hx:y∈generic n)(h:∀ (i:Fin n)(a:Axis), y i a≠ x a) : Points.cons x y∈generic (n+1):=by
    intro a i j; refine Fin.cases (motive:=fun i=> (Points.cons x y) i a = (Points.cons x y) j a→ i=j) ?_ (fun i=> ?_) i
    · refine Fin.cases ?_ (fun k=>?_) j; exact fun _=> rfl; exact fun he => False.elim (h k _ he.symm)
    refine Fin.cases ?_ (fun k=>?_) j; exact fun he=>False.elim (h i _ he)
    exact fun he=> congr_arg Fin.succ (hx a he)
lemma duo_generic (x:E4)(a:Points n)(hx:∀ i:Axis,x i≠0)(j:ℕ) :
    ∃ᶠ y in 𝓝 a, Points.cons x (Points.cons 0 y) ∈ generic (n+2)∧ ∃ k ≥ j, ∃ u, y=Extraction.Order.grid C k u:=by
    let Z:Set (Points n):={y| Points.cons x (Points.cons 0 y)∈generic (n+2)}
    have he : ∀ᵐ y,y ∈ Z := by
       have ht (i:Fin n)(a:Axis)(z:ℝ):∀ᵐ y:Points n,y i a≠z:=by rw [ae_iff]; simpa using plane_price i a z
       filter_upwards [almostGeneric n,ae_all_iff.mpr fun i=>ae_all_iff.mpr fun a=> (ht i a 0).and (ht i a (x a))] with y hy hh
       refine piece_generic _ _ (piece_generic 0 y hy fun i a=>(hh i a).1) (fun i a=> Fin.cases ?_ (fun i=>(?_)) i); exact (hx a).symm; exact (hh _ a).2
    have H : IsOpen Z:= (genericOpen _).preimage (show Continuous (fun y : Points n=> Points.cons x (Points.cons 0 y)) by unfold Points.cons points; fun_prop)
    refine mem_closure_iff_frequently.mp (closure_minimal (s:=Z) (fun i hi=> ?_) isClosed_closure (dense_of_ae he a))
    refine mem_closure_iff_frequently.mpr (((refiner (C:=C) j i).and_eventually (H.mem_nhds hi)).mono fun p h=> ?_)
    exact ⟨h.2,h.1.2⟩
variable {S:Table C.book}(K:Spec.Final C F S)
open Org in
lemma contexts (h:Grill C F)(v:Fin n→ C.book.Token) (g:ℝ)(hg:0 < g) (b:ℕ) : ∃ A:ℝ, 0 < A ∧
   ∀ (ℱ:Filter (ℕ×ℕ)) (_:ℱ.NeBot) (ε:ℝ),0 ≤ ε → ℱ ≤ F.fuse → ∀ j, b ≤ j → ∀ (x:Lattice.Cover) (z:C.label D),
     RealPair B U z b j x ε ℱ → (∀ i:Axis, C.S.gridPoint j x i ≠ 0) →
     ∀ (c:Fin n → Lattice.Cover), Injective (Fin.cons (α:=fun _:Fin (n+1)=> Lattice.Cover) 0 c) → ∀ (y:Points n), (∀ i,atStop C.S b (c i) g (y i)) → Points.cons (C.S.gridPoint j x) (Points.cons 0 y) ∈ conf (n+2) →
       ∀ s:StateIndex K, ‖wordPrice B U z v (C.S.gridPoint j x) y (state K s)‖ ≤ ε*A:=by
   obtain ⟨k,hk,hE,hk'⟩:=((eventually_ge_atTop b).and ((eventually_all.mpr fun i=> services_one (v i) K.room.copies K.room.cutoff).and ((C.S.shrinks.const_mul (3:ℝ)).eventually (ge_mem_nhds (show 3*0<g by simpa using hg))))).exists
   refine ⟨∏ i, headline C k (v i), Finset.prod_pos fun i _=> Real.exp_pos _,fun ℱ _ ε hε hF j hj x z hx hu c hc y hy hz s=>?_⟩
   let T:= state K s; let p:= C.S.gridPoint j x; let V:Set (Points n):={y| ∀ i, atStop C.S b (c i) g (y i)}
   have hv : IsOpen V:=by
      rw [show V=⋂ i:Fin n, {y:Points n | atStop C.S b (c i) g (y i)} from Set.ext fun x=> by simp [V]]; exact isOpen_iInter_of_finite fun i=>(atStop_open ..).preimage (show Continuous (fun y:Points n=> y i) by fun_prop)
   have hW:=hierarchy K s
   have ht: Points.cons (0:E4) y∈conf _:= Points.tail_in hz
   have he (a:E4)(n:ℕ): Continuous (fun y:Points n=>Points.cons a y):=by unfold Points.cons points; fun_prop
   have hI : ContinuousAt (fun y:Points n=> wordPrice B U z v p y T) y:=
      (((T.smooth_read hW.smooth (seatsPair (seatsPair v ⟨d,B⟩) ⟨t,U⟩)).continuousOn.continuousAt ((conf_open _).mem_nhds hz)).comp (he (C.S.gridPoint j x) (n+1)).continuousAt|>.comp (he 0 _).continuousAt).sub (((T.smooth_read hW.smooth (seatsPair v ⟨D,z⟩)).continuousOn.continuousAt ((conf_open _).mem_nhds ht)).comp (he 0 _).continuousAt)
   refine le_of_tendsto_of_frequently hI.norm (((duo_generic (C:=C) p y hu j).and_eventually (hv.mem_nhds hy)).mono fun x' h'=>?_)
   obtain ⟨⟨hX,l,hj',u,rfl⟩,hP⟩:=h'; refine fixed_ports B U z v x u hj' hX K h c hc s hF (hj.trans hj') _ (fun i=>Real.exp_pos _|>.le) ε hε hx fun i=> ?_
   apply Eventually.filter_mono hF
   exact hE i _ l _ _ hk (hj.trans hj') (fun a=> (show _ < _ - g from hP i a).trans_le (by linarith only [show 3*C.S.a k ≤ g from hk']))
end YM.Frontier6.Platform
