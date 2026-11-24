import YM.RegulatorIR.Sources.Roll

/-!
# Exact centered root restoration

Torus lift, no canonical invocation escape on infinite Cover. Root-sup test in
own spacing coordinates. Child path aligns with centered-map preimage average.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Sources
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W J X Y A B: Type}{q u b p a i j e k d m r:ℕ}{M: W→ℕ}{n:Page M→Side}{L:Meter W}{D:Choice M}
variable {S:Heir n G} (R:Reel S)
section Grid

-- branch epoch geometry
def child (L:Side) (x:Cover)(s:Site L) : Cover:= L.val • x + Lattice.lift s
lemma countR {L:Side}{u v:Cover}{x y:Site L}(h:child L u x=child L v y): u=v ∧ x=y:=by
 have ht w (x:Site L):wrap L (child L w x)=x:= by apply Eq.trans (congr_arg (Prod.fst: Edge (Site L)→Site L) (channel_dep L w (Lattice.lift x,0))); exact wrap_lift x
 have hz:x=y:=(ht u x).symm.trans ((congr_arg (wrap L) h).trans (ht v y)); subst y; exact ⟨smul_right_injective Cover (by exact_mod_cast L.property.ne') (add_right_cancel h),rfl⟩
lemma reachesR (L:Side)(x:Cover) : ∃ w : Cover × Site L,child L w.1 w.2=x:=by
 let z:=Lattice.lift (wrap L x)
 obtain ⟨w,h,hh⟩:= channel_eq L (z,0) (x,0) (Prod.ext (wrap_lift _) rfl); exact ⟨(w,wrap L x), congr_arg (Prod.fst : Edge Cover→Cover) h.symm⟩

def claims (L:Side): Cover × Site L≃ Cover:= Equiv.ofBijective (fun x=> child L x.1 x.2) ⟨fun _ _ h=> Prod.ext (countR h).1 (countR h).2,reachesR L⟩
end Grid
abbrev gaze (φ:Room→ℝ)(s:ℝ)(y:Room)(x:Room):ℝ:= φ (y+s • x)
abbrev perch (φ:Room→ℝ)(v:ℝ)(x:Room)(s:Cover):Room→ℝ:=gaze φ v (slide v s-x)
def calling (s:Side)(φ:Room→ℝ)(x:Site s):Room→ℝ:=gaze φ ((s.val:ℝ)⁻¹) (((s.val:ℝ)⁻¹) • slide 1 (Lattice.lift x))
lemma beamAt {φ: Room→ℝ}(hp: ContDiff ℝ p φ) {k :ℕ}(he:k ≤ p)(s:ℝ)(y:Room)(x:Room)(v :Fin k→Room) : iteratedFDeriv ℝ k (gaze φ s y) x v=s^k * iteratedFDeriv ℝ k φ (y+s • x) v:=by
 let g (x:Room):= φ (y+x);let A : Room →L[ℝ] Room := s • ContinuousLinearMap.id ℝ Room
 rw [show gaze φ s y=g ∘ A from rfl,A.iteratedFDeriv_comp_right (f:=g) (hp.comp (contDiff_const.add contDiff_id)) _ (by exact_mod_cast he), ContinuousMultilinearMap.compContinuousLinearMap_apply,show iteratedFDeriv ℝ k g _= iteratedFDeriv ℝ k φ _ from iteratedFDeriv_comp_add_left ..]; change iteratedFDeriv ℝ k φ (y+s • x) (fun i=>s • v i)=_; rw [ContinuousMultilinearMap.map_smul_univ]; simp
lemma twig (l:Flap M)(φ:Room→ℝ)(x:Room)(s:Cover)(i:Site (R.steps l).patch.L): calling (R.steps l).patch.L (perch φ (S.l l.next) x s) i= perch φ (S.l l.prev) x (child (R.steps l).patch.L s i):=by
 ext1 v; apply congr_arg φ
 let a:=(R.steps l).patch.L; let A:ℝ:= a.val; let t:=Lattice.lift i
 have he : A≠0:=by unfold A; positivity
 rw [child,map_add,← show slide (S.l l.next) s= slide (S.l l.prev) (_ • s) from indentX R l s, scaledCard R]
 ext1 b; change (S.l l.prev * A) * (s b:ℝ)-x b + ((S.l l.prev * A) * (A⁻¹*(1*(t b:ℝ))+A⁻¹*v b))=((S.l l.prev * A)*(s b:ℝ)+S.l l.prev*(t b:ℝ))-x b+S.l l.prev*v b
 field_simp;ring

-- transport localized mark by nested root coordinates
abbrev rebaseO (t:Cover)(A:Orders (Foot G)):Orders (Foot G):= fun i j=> echo (carryX t) (A i j)
lemma rootR (t:Cover)(L:Orders (Foot G))(w:Cover): rebaseO t (rebaseO w L)= rebaseO (t+w) L:=by
 ext e r x; unfold rebaseO echo
 apply congr_arg; ext1 i
 refine Prod.ext ?_ rfl; refine Prod.ext ?_ rfl
 change -w+(-t+ _) = -(t+w)+_;abel

lemma echoApply (V:Orders (Foot G))(x:Cover)(s:ℝ): rebaseO x (s • V)= s • rebaseO x V:=rfl
lemma echoes_sum (s:Finset J)(V:J→Orders (Foot G))(x:Cover): rebaseO x (∑ i∈s,V i)=∑ i∈s,rebaseO x (V i):=by ext1 i; ext1 j;ext1 b; unfold rebaseO echo; simp only [Finset.sum_apply]
lemma echoBill (x:Cover)(V:Orders (Foot G))(h:Cluster.Bill V p): Cluster.Bill (rebaseO x V) p:=by
 intro i he a
 rw [← show quota (V i a) 1=quota (rebaseO x V i a) 1 from ?_]; exact h i he a
 unfold quota; rw [← (Tuple.winding (carryX (G:=G) x) a).tsum_eq (f:=fun b:Tuple (Foot G) a=>‖rebaseO x V i a b‖ₑ*(1:Tuple (Foot G) a→ℝ≥0∞) b)]; apply tsum_congr;intro b;apply congr_arg₂ (· * ·)
 · exact congr_arg (fun z:ℝ=>‖z‖ₑ) (echos (carryX x) (V i a) b).symm
 rfl
section Odyssey
variable {T:S.Accounts} (H:Passage R) (hc:Common R)(hp:R.Follows T)
include H hc hp
lemma eachRebase (x:Cover)(B:Orders (Foot G))(m:ℕ)(w:Flap M):
 rebaseO x ((S.frames w).each m (T.bulk w.prev) B)= (S.frames w).each m (T.bulk w.prev) (rebaseO (strideR (R.steps w) x) B):=by
 ext1 i; ext1 j; symm; exact Echos.only (flames _ _ (H.cells hc hp w.prev _) (H.levels w x).1 (H.levels w x).2 (Passage.assets hc w x) (fun _ _=> echos _ _) i j)
end Odyssey
end YM.RegulatorIR.Sources
