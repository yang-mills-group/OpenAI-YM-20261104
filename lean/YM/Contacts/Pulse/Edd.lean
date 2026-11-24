import YM.Contacts.Pulse.Square
import YM.Push.FREE_RESOLVENT.FullRow
namespace YM.Pulse.Spine
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Extension.UV.Linear
open scoped Classical Topology BigOperators NNReal ENNReal Matrix
noncomputable section
variable {α β X Y : Type} {m:ℕ→Side}{C D:ℝ}{σ:ℝ≥0}
section inverse
variable [Fintype α][DecidableEq α]
lemma garth (X:CompM α α) (hC:0≤C)(h:∀ i j, ‖X i j‖≤C) : vflux X≤ Fintype.card α * (Fintype.card α*C) := by
  apply flux_price (by positivity); intro u v
  let w i j:= u i * (X i j*v j); simp only [Matrix.mulVec,dotProduct,mul_sum]; apply (norm_sum_le ..).trans
  let d:= slug u*C*slug v
  have he (i:α)(j:α): ‖w i j‖≤ d:= by unfold w d; rw [norm_mul,norm_mul,mul_assoc]; exact mul_le_mul (slug_atom ..) (mul_le_mul (h i j) (slug_atom ..) (norm_nonneg _) hC) (by positivity) (slug_nonneg _)
  apply le_trans (sum_le_sum (fun i (_:i∈Finset.univ)=> le_trans (norm_sum_le ..) (sum_le_sum (fun j _=>he i j)))) _; simp only [sum_const,card_univ,nsmul_eq_mul]; unfold d; ring_nf; rfl
lemma inv_flip_star (A:CompM α α): (A.map star)⁻¹=(A⁻¹).map star:= by
  rw [← Matrix.transpose_conjTranspose, ← Matrix.conjTranspose_nonsing_inv, ← Matrix.transpose_nonsing_inv, Matrix.transpose_conjTranspose]
structure Cabinet (U V:Row α α): Prop where
  r n : U.acts n* V.acts n=1
  l n : V.acts n* U.acts n=1
lemma cabin_inverse {A:Row α α} (h:Row.strip A σ C)(hs:0<σ)(hD:0<D)(hm:Tendsto (fun j=>(m j).val) atTop atTop)(he:∀ i,(A.acts (m i))ᵀ=A.acts (m i))(hi:∀ i,FreeResolvent.Gap (A.acts (m i)) D)(p:Momentum)(hx:star p=p): Stable (A.read p) D := by
  let X:= A.read; apply stable_real; intro x
  let f (y:Momentum):= ((dotProduct (star x) (A.read y*ᵥ x)).re); change _≤ f p
  obtain ⟨k,u,hu,hK⟩ := mesh_stride m hm p hx
  have hσ : 0<(σ:ℝ):=hs; have hV a b : Firm σ C (fun y:Momentum=>A.read y a b):= Firm.of_series (A.constant_strip h _ _) hσ; have hl := Work.F07.realStrip _ hσ hx
  have hA : ContinuousAt f p := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_finsetSum Finset.univ (fun i _=> Tendsto.const_mul ((star x) i) (tendsto_finsetSum Finset.univ (fun j _=> (((hV i j).1.hol p hl).continuousAt.tendsto.mul_const (x j))))))
  apply ge_of_tendsto (hA.tendsto.comp hu) (Eventually.of_forall fun i=>?_); apply credit_plane A (Whole.safe ⟨_,_,hσ,h⟩) (he _) (A:= Fintype.card α*C) _ x (k i) (u i) (hK i); intro v; refine ⟨(hi i).lower _,?_⟩; apply le_trans (le_abs_self _) (FreeResolvent.schur_qf _ _ (FreeResolvent.physical (s:=0) (strip_mono h (by positivity) le_rfl) le_rfl _) _)
lemma cabinet (α:Type)[Fintype α][DecidableEq α](σ:ℝ≥0)(C D:ℝ)(hs:0<σ)(hC:0≤C)(hD:0<D) : ∃ (η:ℝ≥0)(T:ℝ),0<η∧ 0≤T ∧ ∀ (A:Row α α), A.strip σ C → ∀ m:ℕ→Side, Tendsto (fun j=>(m j).val) atTop atTop → (∀ i,(A.acts (m i))ᵀ=A.acts (m i)) → (∀ i,FreeResolvent.Gap (A.acts (m i)) D) → ∃ V:Row α α, V.strip η T ∧ Cabinet A V := by
  have hσ : 0<(σ:ℝ):=hs
  obtain ⟨η,K,hη,he,hK,H⟩:= shelter (σ:ℝ) (Fintype.card α*(Fintype.card α*C):ℝ) 1 D hσ (by positivity) (by norm_num) hD
  lift η to ℝ≥0 using hη.le; let t :ℝ≥0:=η/3; have ht : 0<(t:ℝ):= by unfold t; push_cast; positivity
  let z:= K*(2*((1+(t:ℝ))/(t:ℝ)))^(Fintype.card Axis); refine ⟨t,z,NNReal.coe_pos.mp ht,by unfold z; positivity,fun A h m hm hu hG=> ?_⟩
  let X:= Slab.basic α
  let f:= A.read; have hf i j := Firm.of_series (A.constant_strip h i j) hσ
  have hP:Poster σ f:= ⟨fun {p} w i j=> (hf i j).1.hol p w,fun x _=> by obtain ⟨y,rfl⟩:=x; exact (A.periods ..).symm⟩
  have hX : Freezer X X f η K := H _ X X Slab.Height.basic Slab.Height.basic f hP (fun p hp=> by simpa only [X, serial,carryM, Slab.basic,inv_one,Matrix.one_mul,Matrix.mul_one] using garth (f p) hC fun i j=>(hf i j).2 _ hp) (fun p x=> by simpa only [X, serial, carryM,Slab.basic,inv_one,Matrix.one_mul,Matrix.mul_one] using cabin_inverse h hs hD hm hu hG p x)
  let g (p: Momentum):= (f p)⁻¹; have hg i j: Vane (fun p=> g p i j) η:= ⟨hη, fun p w=> (BillD.take (hP.shape (fun i=> (w i).trans_le he)) (hX.period p w)) i j,fun p w x => by dsimp only [g,f]; rw [A.periods]⟩
  have hv (i j:α) (p: Momentum) (w:p∈ strip (η:ℝ)): ‖g p i j‖ ≤ K:= (flux_tilt (g p) i j).trans (by let h:=hX.price p w; simpa only [serial,X,carryM,Slab.basic,inv_one,Matrix.one_mul,Matrix.mul_one] using h)
  let u i j p:= g p i j; let V : Row α α:= fun i j x=> (market (u i j) 0 x).re
  have hw i j: Width t z (market (u i j) 0) := (hg i j).issues (hv i j) t t ht.le ht (by unfold t; push_cast; linarith only [hη])
  have hV : V.strip t z:= fun i j=> Work.F07.widthRealPart (hw i j); refine ⟨V,hV,?_⟩
  have hx p (hp:star p=p): V.read p=g p:= by
     have hh:star (-p)=-p:= by rw [star_neg,hp]
     ext i j; change Laurent.read _ p=u i j p; rw [Work.F07.readRealPart (hw i j) ht hp,(hg i j).paints (hv i j) p (Work.F07.realStrip _ hη hp),(hg i j).paints (hv i j) (-p) (Work.F07.realStrip _ hη hh)]; unfold u g f; rw [show A.read (-p)= _ from (show A.read (-p)=(A.read p).map star by simpa only [hp] using A.conjugate p),inv_flip_star]; simp
  have ha: Whole A:= ⟨_,_,hσ,h⟩; have hb: Whole V:=⟨_,_,ht,hV⟩
  have hh n : A.acts n*V.acts n=1:= by
    rw [← ha.acts hb,← acts_unit]; apply Whole.eq_on (ha.prod hb) (Whole.coin _) (fun p hp=> ?_)
    rw [ha.read hb hp.1,hx p hp.1,read_unit]; exact Matrix.mul_nonsing_inv _ (hX.period p (Work.F07.realStrip _ hη hp.1))
  exact ⟨hh, fun i=> mul_eq_one_comm.mp (hh i)⟩
variable {A A' B B':Row α α}
lemma borrow_difference (h: Cabinet A B)(hp: Cabinet A' B')(ha:Whole A)(ha':Whole A')(hb:Whole B)(hb':Whole B') : minusRows B B'=composeRows (composeRows B (minusRows A' A)) B':= by
  let z:= hb.prod (ha'.minus ha); apply bank_injective (hb.minus hb').safe (z.prod hb').safe; intro n; rw [z.acts hb',hb.acts (ha'.minus ha),ha'.less ha,hb.less hb',Matrix.mul_sub,Matrix.sub_mul, h.l,Matrix.one_mul,Matrix.mul_assoc,hp.r,Matrix.mul_one]
end inverse
end
end YM.Pulse.Spine
