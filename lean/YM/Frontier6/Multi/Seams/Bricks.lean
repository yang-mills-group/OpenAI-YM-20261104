import YM.Frontier6.Multi.Seams.Avoid

/- No regularity in the center program as clearance vanishes assumed. Here at
   fixed disjoint positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Set Finset Filter Lattice RG Wilson Extraction Cells Next.UVStress Bid Spec Platform Tale OS Word
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C: Family G}{V:Type}[Fintype V][DecidableEq V]
lemma falling (k:ℕ)(z:V→ E4): ∃ᶠ y in 𝓝 z, ∃ (m:ℕ), k ≤ m∧ ∃ p:V→ Cover, y=C.S.gridPoint m ∘ p:=by
    let M:= Fintype.card V; let e:= Fintype.equivFin V; let p' : Points M:= points (z ∘ e.symm); let x (y:Points M):V→ E4:= fun i=> y (e i)
    have hp: Continuous x:=by unfold x; fun_prop
    have he:x p'=z:=by ext1 i; simp [x,p']
    refine (he ▸ hp.continuousAt.tendsto (x:=p') : Tendsto x (𝓝 p') (𝓝 z)).frequently ?_
    refine (refiner (C:=C) k p').mono ?_
    rintro y ⟨hy,j,hj,u,rfl⟩; refine ⟨j,hj,u ∘ e,?_⟩; rfl

variable {k m l:ℕ}{P:V→Type} {W : (i:V)→P i→Type}
variable (X:∀ i:V,Plan C (P i) (W i)) [_i : ∀ i,Fintype (P i)] [_j : ∀ i b,Fintype (W i b)]
variable {F:Extraction.Order}{S: Table C.book} (K:Final C F S)(s:StateIndex K)
set_option quotPrecheck false
local notation "ι"=> (∀ i:V,P i)
namespace Plan
variable (z:V→ E4) (v:V→ Cover) (π:V→ℝ) (r:V→ℕ) {ξ:Filter (ℕ×ℕ)}[ξ.NeBot](hf:ξ ≤ F.fuse)
local notation "W'"=> fun z:V → E4=> poll S (state K s) (∏ i:V,(X i).syntaxR k (z i) S)
variable (hw:∀ i,0 ≤ π i) (hB:∀ i:V,l ≤ r i)
    (hp:∀ x:V, ∀ᶠ i:ℕ×ℕ in ξ,∃ h:r x ≤ i.1,let T:=center C.S i.2 h 0; Interior (T.chamber 0) ((X x).cost k i.1 i.2) ∧ T.rootTest (C.beta i.1 i.2) ((X x).cost k i.1 i.2) ≤ π x) (hr:Org.Grill C F)
include hr hw hB hp hf
lemma pairs (hv : Injective v) (ht:∀ i:V, atStop C.S l (v i) (3*C.S.a (r i)) (z i)) (hD:∀ p:ι,Injective (landing X k z p)) (hc:∀ i,SlotsClear (X i) k) : ‖W' z‖≤∏ i:V,π i:=by
    apply le_of_tendsto_of_frequently ((reads_cont X K s hD).norm)
    let x : Set (V→ E4):={z| clearFamily X k z}
    have hy : ∃ᶠ s in 𝓝 z,s∈ x∧ ∃ (m:ℕ), max k l ≤ m∧ ∃ p:V→ Cover,s=C.S.gridPoint m ∘ p:= by
       rw [← frequently_frequently_nhds]; refine (mem_closure_iff_frequently.mp (dense_scene X hc z)).mono fun y hy=>?_; exact ((falling (C:=C) (max k l) y).and_eventually ((intact X k).mem_nhds hy)).mono fun _ h=>⟨h.2,h.1⟩
    let P:V→Set E4:= fun i=> {x| atStop C.S l (v i) (3*C.S.a (r i)) x}
    refine (hy.and_eventually (eventually_all.mpr fun i=> ((continuous_apply i).continuousAt (x:=z)).eventually (p:=fun p=>p∈P i) ((atStop_open ..).mem_nhds (ht i)))).mono ?_
    rintro y ⟨⟨he,k,H,c,rfl⟩,h⟩; exact pays X c ((le_max_left ..).trans H) he K s hr hf ((le_max_right ..).trans H) v hv π r hw hB h hp
omit hB

lemma slots_bill (h:∀ (z:V→ E4),∃ p:E4, ∃ v:V→ Cover,∀ i:V, atStop C.S l (v i) (3*C.S.a (r i)) (z i+p)) (hz: Pairwise (fun i j=>4*C.S.a l < ‖z i-z j‖)) (hD:∀ p:ι,Injective (landing X k z p))(hB:∀ i:V,l ≤ r i) (hc:∀ i,SlotsClear (X i) k): ‖W' z‖≤∏ i:V,π i:=by
    obtain ⟨p,v,hv⟩:=h z; let x(i:V):=z i+p
    have he: Injective v:=by
       let E:=Fintype.equivFin V; let y:= points (z ∘ E.symm)
       -- fit margin uniform 0 too. use clock relay
       have hg:Injective (v ∘ E.symm):= distinct_stops C.S y (show MergeProof.Ribbons.slide C.S l y from (fun i j h=> hz (E.symm.injective.ne h.symm))) le_rfl p (v∘ E.symm) (fun i j=> lt_of_lt_of_le (hv (E.symm i) j) (sub_le_sub_left (mul_nonneg (by norm_num) (C.S.a_pos _).le) _))
       exact (Equiv.injective_comp E.symm v).1 hg
    have ha (u):Injective (landing X k x u):= by unfold landing x; simp_rw [← add_assoc]; exact fun i j h=> hD u (add_right_cancel (show _+p=_+p from h))
    dsimp only; rw [← reads_move X K s p]; exact pairs X K s x v π r hf hw hB hp hr he hv ha hc
end Plan
end YM.Frontier6.Road
