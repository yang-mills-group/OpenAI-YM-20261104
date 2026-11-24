import YM.GapsR2RG.Setting
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Ghost
/-!
# Affine-null vacuum directions as scalable field-column perturbations

Precursor to a stable-difference estimate using the actual column tools on
complete insertions. Adapt the PMOM/Weighted and JointLoad Heir Ghost argument
in the converse direction. Degree 4 is not a cutoff on perturbation order!
It charges engineering to get Δ^4 × a stability gain and use volume anchors.
Keep actual masks and denominator at the linearization point.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open Lean
namespace YM.GapsR2RG.Anchor
open Lattice Wilson RG RG.Activities PhysicalNext PhysicalNext.JointLoad.Heir
open Labels Source Function Filter Set MeasureTheory Finset
open MultiNext MultiNext.SignedSource MultiNext.SignedSource.Mediator
open scoped Classical Topology Matrix.Norms.Frobenius ContDiff BigOperators
set_option quotPrecheck false

variable {T X Y Z:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]
  [NormedAddCommGroup Y][NormedSpace ℝ Y]
  [NormedAddCommGroup Z][NormedSpace ℝ Z]
-- direct converse to extraction direction used in PMOM
lemma held_comp (A:ℕ→Set X)(B:ℕ→Set Y)(n:ℕ){f:X→Y}{g:Y→Z}(hf:ContDiffAt ℝ (↑n:ℕ∞ω) f 0)(hg: ContDiffAt ℝ (↑n:ℕ∞ω) g 0)
   (h0:f 0=0) (hE:Mediator.valence B n g)(hB:Mediator.curry A B n f):Mediator.valence A n (g ∘ f) := by
  intro m α u hu
  have hx : m≤ n := by
      have hv := Finset.sum_le_sum (s:=Finset.univ) (f:=fun _=> (1:ℕ)) (fun i _=> (hu.1 i).1)
      simpa using hv.trans hu.2
  rw [iteratedFDeriv_comp (h0.symm ▸ hg) hf (by exact_mod_cast hx),h0,FormalMultilinearSeries.taylorComp,_root_.sum_apply]
  simp_rw [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,OrderedFinpartition.applyOrderedFinpartition_apply,ftaylorSeries]
  apply Finset.sum_eq_zero
  intro p _
  let d (i:Fin p.length) := ∑ r, α (p.emb i r)
  have ht(i:Fin p.length): Mediator.Axes A n (α ∘ p.emb i) (u ∘ p.emb i):=⟨fun r=>hu.1 _,by
       change d i≤ _; exact (Finset.single_le_sum (s:=Finset.univ) (f:=d) (fun j _=>Nat.zero_le _) (Finset.mem_univ _)).trans (le_trans (le_of_eq (p.sum_sigma_eq_sum α)) hu.2)⟩ -- rw useless
  refine hE _ d _ ⟨fun i=>⟨?_,hB _ (p.partSize_pos _) _ _ (ht i)⟩, (le_of_eq (p.sum_sigma_eq_sum α)).trans hu.2⟩
  letI : Nonempty (Fin (p.partSize i)):= Fin.pos_iff_nonempty.mp (p.partSize_pos i)
  unfold d
  exact sum_pos (s:=Finset.univ) (f:=fun r=>α (p.emb i r)) (fun r _=> (hu.1 (p.emb i r)).1) Finset.univ_nonempty

variable {G:Gauge}{n:Side}{P:BudgetPoint}{S:Support n}{o:Site n}
-- no constants on derivatives asked here. actual germs only.
-- keep calculus polymorphic to avoid reduction of the actual jet space while checking the multilinear identities
private lemma probeMap {D: Type} (V:Fin (4-1) → Type) [NormedAddCommGroup D][NormedSpace ℝ D] [∀ j,NormedAddCommGroup (V j)][∀ j,NormedSpace ℝ (V j)]
    (c:∀ j,V j) (x:ℝ→ D × (∀ j,V j)) (hx: x=fun t=> (0,fun i=>t^(i.val+2) • c i)) :
    ContDiff ℝ 4 x ∧ x 0=0 ∧ ∀ m : ℕ, (0 < m) → (m ≤ 4) → ∀ u : Fin m → ℝ,
      ((iteratedFDeriv ℝ m x 0 u).1=0 ∧ ∀ i:Fin (4-1),m < (i.val+2) → (iteratedFDeriv ℝ m x 0 u).2 i=0) :=by
  let E:= D × (∀ j,V j)
  have hz {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V](u:V)(k:ℕ):ContDiff ℝ 4 (fun t:ℝ=>t^k • u):=(contDiff_id.pow _).smul contDiff_const
  have hf : ContDiff ℝ 4 x:=by rw [hx]; apply ContDiff.prodMk contDiff_const; exact contDiff_pi.mpr (fun j=> hz (V:=V j) _ _)
  have h0 : x 0=0:= by rw [hx]; exact congr_arg (Prod.mk (0:D)) (funext (fun i=>by rw [zero_pow (by omega),zero_smul]; rfl))
  refine ⟨hf,h0,fun m hm hM u=>?_⟩
  have he {V:Type}[NormedAddCommGroup V][NormedSpace ℝ V](q:E→L[ℝ] V)(hq:iteratedDeriv m (q ∘ x) 0=0): q (iteratedFDeriv ℝ m x 0 u) = 0 :=by
      have h' := q.iteratedFDeriv_comp_left (x:=0) hf.contDiffAt (show (m:ℕ∞ω)≤4 from Nat.cast_le.mpr hM)
      change iteratedFDeriv ℝ m (q ∘ x) 0 = _ at h'
      have hv : iteratedFDeriv ℝ m (q ∘ x) 0 (fun _=>1)=0:=hq
      have h₁:u = fun i=> u i • (1:ℝ):= funext fun i=> (mul_one (u i)).symm
      change (q.compContinuousMultilinearMap _) u=0
      rw [← h']
      nth_rw 1 [h₁]
      rw [ContinuousMultilinearMap.map_smul_univ,hv,smul_zero]
  let q : E →L[ℝ] D := ContinuousLinearMap.fst ..
  refine ⟨he q (by rw [hx,show q ∘ (fun t:ℝ=> _) = fun t:ℝ=>(0:D) from rfl]; simp),fun j hj=> ?_⟩
  let q':E →L[ℝ] (V j):= (ContinuousLinearMap.proj (R:=ℝ) (φ:=V) j).comp (ContinuousLinearMap.snd ℝ D (∀ j,V j))
  change q' _ = 0
  have hh : iteratedDeriv m (q' ∘ x) 0=0 := by
    rw [hx,show q' ∘ (fun t:ℝ=>_) = fun t:ℝ=>t^(j.val+2) • c j from rfl]
    rw [iteratedDeriv_smul_const (contDiffAt_id.pow _), iteratedDeriv_fun_pow_zero]
    simp only [if_neg (by omega : m ≠ j.val+2),Nat.cast_zero,zero_smul]
  exact he q' hh

lemma boundedArc {J:Jet G} {v:ℝ→Mom.Slate G n 4}(h: ∀ t, v t = (0, Drops.trunk 4 (scaleJet J t))) : ContDiffAt ℝ 4 v 0 ∧ v 0=0 ∧
      Mediator.curry (fun _=> Set.univ) (fun i=> (Mom.Sites o S i (G:=G) (d:=4): Set (Mom.Slate G n 4))) 4 v:=by
  let E:= Mom.Slate G n 4
  letI : NormedAddCommGroup E := inferInstanceAs (NormedAddCommGroup ((Site n → G.Color) × Drops.Snap G 4))
  letI : NormedSpace ℝ E := inferInstanceAs (NormedSpace ℝ ((Site n → G.Color) × Drops.Snap G 4))
  obtain ⟨hf,h0,hq⟩:= probeMap (fun i=>Taylor G i.val) (fun i=>J i.val) v (funext h)
  refine ⟨hf.contDiffAt,h0,fun m hm α u hu=>?_⟩
  have hx:m≤∑ i,α i := by simpa using (Finset.sum_le_sum (s:=Finset.univ) (f:=fun _=> (1:ℕ)) fun i _=>(hu.1 i).1)
  exact ⟨⟨(0:E4→G.Color), (Powers.space E4 G.Color _).zero_mem, fun i _=>congr_fun (hq m hm (hx.trans hu.2) u).1 i⟩,fun j hj=> (hq m hm (hx.trans hu.2) u).2 _ (hx.trans_lt hj)⟩

lemma survey (H:Hol G) (g:Config G n→ℝ) (hg: G.Simple) (hX:Seed P o S g)(hs:Nonwrapping S o)(hn:4≤n.val): H.PiVanish 4 o (Complex.ofReal ∘ g) :=by
   intro J F
   let E:=Mom.Slate G n 4; let x:ℝ→E:=fun t=> (0,Drops.trunk 4 (scaleJet J t))
   let ξ:= (g ∘ increment (1:Config G n)); let Φ:= Mom.optic S o (G:=G) (d:=4); let f:ℝ→ℝ:=fun t=> g (H.testLinks 4 o J t)
   obtain ⟨hC,hx,H0⟩:=boundedArc (o:=o) (S:=S) (v:=x) (fun _=>rfl)
   have hϕ:= Mom.osmotic (G:=G) (d:=4) S o
   have hξ : ContDiffAt ℝ 4 ξ 0:= (hX.good.smooth (1:Config G n) (Next.Foundations.one_healthy S P.threshold P.threshold_pos.le)).of_le (show (4:ℕ∞ω)≤P.order by have hs:=P.order_ge; exact_mod_cast le_trans (by decide : 4≤6) hs)
   have ha := ((hϕ.2.symm ▸ hξ).comp 0 (f:=Φ) (hϕ.1.of_le (show (4:ℕ∞ω)≤_ from le_top)))
   have hp := (hx.symm ▸ ha).comp (0:ℝ) (f:=x) hC
   have hval:=held_comp (Z:=ℝ) (fun j=>(Mom.Sites o S j (G:=G) (d:=4):Set E)) (fun j=>(Mom.Maps o S j (G:=G):Set (Directions G n))) 4 (hϕ.1.of_le le_top) hξ hϕ.2 (hX.four hg hs hn) (Mom.along o S (show 2≤n.val by omega) hs)
   have ht := held_comp (fun _=>Set.univ) (fun j=>(Mom.Sites o S j (G:=G) (d:=4):Set E)) 4 hC ha hx hval H0
   have he : ((Complex.ofReal ∘ g) ∘ increment 1) ∘ Φ =ᶠ[𝓝 0] (fun q=> (Complex.ofReal ∘ g) (H.testLinks 4 o (Drops.expand 4 q.2) 1)) := Mom.appears (fun _ _ hy=> congrArg Complex.ofReal (hX.good.sites _ _ hy)) (fun k U=> congrArg Complex.ofReal (hX.good.symmetry k U)) H
   have hF : (ξ ∘ Φ) ∘ x =ᶠ[𝓝 0] f:=by filter_upwards [he.comp_tendsto (show Tendsto x _ (𝓝 0) from hx ▸ hC.continuousAt)] with i hi; change Complex.ofReal _ = Complex.ofReal _ at hi; change _ = Complex.ofReal (g (H.testLinks 4 o (Drops.expand 4 (Drops.trunk 4 (scaleJet J i))) 1)) at hi; rw [← YM.Next.Foundations.test_scaled] at hi; exact Complex.ofReal_inj.mp hi
   have hq : ContDiffAt ℝ 4 f 0:= hp.congr_of_eventuallyEq hF.symm
   refine ⟨Complex.ofRealCLM.contDiff.contDiffAt.comp 0 hq,fun i hi=>?_⟩
   change iteratedDeriv i (Complex.ofReal ∘ f) 0=0
   have hfn : iteratedFDeriv ℝ i f 0 (fun _=>1)=0:=(congr_arg (· (fun _=>1)) ((hF.symm.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds)).trans (ht i (fun _=>1) (fun _=>1) ⟨fun _=>⟨le_rfl,trivial⟩,by simp; exact hi⟩) -- placeholder
   unfold iteratedDeriv; change iteratedFDeriv ℝ i (Complex.ofRealCLM ∘ f) 0 (fun _=>1)=0
   rw [Complex.ofRealCLM.iteratedFDeriv_comp_left hq (by exact_mod_cast hi)]; change (iteratedFDeriv ℝ i f 0 (fun _ : Fin i=>1):ℂ) = _; rw [hfn, Complex.ofReal_zero]
lemma fit {R:Rep G n}(g:Config G n→ℝ)(h:Seed R.p o S g)(hc:G.Simple)(hn:4≤n.val): Extra.Histories.RegFit R o 4 (Next.Foundations.hol G) S (Complex.ofReal∘ g):=⟨PhysicalNext.Repeat.Blush.ornate h.good, h.site, by change Complex.ofReal _=_; rw [h.value]; rfl, fun hs=> survey _ g hc h hs hn⟩
end YM.GapsR2RG.Anchor
