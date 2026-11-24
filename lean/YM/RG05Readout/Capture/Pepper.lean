import YM.RG05Readout.Many.View
import YM.RG05Readout.Capture.Graces
import YM.MergeProof.North.Shasta
/-!
# Preimage postage at arbitrary acquired Blade

No counter stuffed here; works at any threshold. Includes unmasked probe
for Log units. Rolling to Publication has both raw and trajectory stamp here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Finset Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Marker Address
open PhysicalNext.Repeat Lotus MergeProof.Float Motion
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G:Gauge}{n d N m p:ℕ}{C:Family G}
local notation "Z" => C.path.levels
local notation "X"=> C.path.rep N p (m+1)
local notation "Y"=> C.path.rep N p m
local notation "L"=> C.path.S.block m
local notation "ξ"=> C.labels.level
local notation "P"=> C.localSection
variable (H: History G) (A:Hol G)(B:SectionData ((Labels.frames G).level d)) -- use general Family Frame. Grow_stretch require for pure.`Joint` labels unknown. Must generalize stamps.
-- Generic Gig.stretch for any Frame (Shasta is explicit) via Tab primitives.

variable {D:GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)} {x y z s e a v:ℝ}
local notation "Ω"=> C.path.levels.clock.op m p
local notation "Y!"=> Local
-- general instead stamped
section
variable {G:Gauge}{n:Side}{R:Rep G n}{F:Labels.Frame G d}{J:Coefficient F n}
lemma stampedRow (h:Tab J 0 R x y z)(c:ℂ) : Tab (Extra.Histories.stretch c J) 0 R x (‖c‖*y) (‖c‖*z):=by
   obtain ⟨e,he,ht⟩:= h.regular; obtain ⟨f,hf,hy⟩:=h.forced
   refine ⟨h.divisor,mul_nonneg (norm_nonneg _) h.first,mul_nonneg (norm_nonneg _) h.second, ⟨fun i=> ‖c‖*e i,?_,fun i=> Next.Foundations.bound_smul c (ht i)⟩,fun i=> ‖c‖ *f i,?_,fun i=>⟨mul_nonneg (norm_nonneg _) (hy i).1,fun U=> ?_⟩⟩
   · simp_rw [mass_scale];exact Extra.Histories.budget_scale he (norm_nonneg _)
   · simp_rw [mass_scale,mul_left_comm x ‖c‖ z]; exact Extra.Histories.budget_scale hf (norm_nonneg _)
   rw [show (Extra.Histories.stretch c J).forced i U=c • J.forced i U from rfl,norm_smul]; exact mul_le_mul_of_nonneg_left ((hy i).2 U) (norm_nonneg _)
end
variable {K:Site (C.path.S.side (m+1) p)} {f g: Goods G (C.path.S.side (m+1) p)} {k:Res G (C.path.S.side (m+1) p)} {Z':Set Wing}
local notation "Π"=> Along (P d) C.path N p m C.params K
lemma swingEye (h : (Π) Z' D f g k 0 0 x x y)(c:ℂ)(hp:Integrable f (prior G _)) : (Π) Z' D (c • f) (c • g) (c • k) 0 0 (‖c‖*x) (‖c‖*x) (‖c‖* y):=by -- like Shasta
    obtain ⟨Q,hQ,hE⟩:=h; let U:= Extra.Histories.stretch c Q
    refine ⟨U,⟨stretch_format _ hQ.format,?_,?_,?_⟩,?_⟩
    · have hx: U.density 0 (P d) Y = c • Q.density 0 (P d) Y:=by funext i;exact stretch_density ..
      rw [hx,hQ.agrees]; unfold Extra.Histories.blast; rw [StepData.push_smul _ _ _ _ hp,smul_smul,smul_smul,mul_comm c]
    · have hu:=hQ.leadP; rw [sub_zero] at hu; rw [sub_zero]; rw [show U.x=c • Q.x from rfl,Size.smul,mul_left_comm _ ‖c‖ _]; exact mul_le_mul_of_nonneg_left hu (norm_nonneg _)
    · obtain ⟨b,t,hf,ht⟩:=hQ.future; refine ⟨_,_,stampedRow hf c,?_⟩; rw [mul_left_comm _ ‖c‖ _,← mul_add]; exact mul_le_mul_of_nonneg_left ht (norm_nonneg c)
    have he:= hE.travel c; rw [mul_zero,← profile_scale] at he; exact he
structure Plated (T:Labels.Frame G d)(H:History G)(B:SectionData T) (A:Source.Hol G) (m N p:ℕ)(D:GaugeDoor (H.rep N p (m+1)) (H.rep N p m))(x:ℝ):Prop where
   buys (o:Site (H.S.side (m+1) p)) (Q:Set Wing)(M:Leaf (H.rep N p (m+1))): (H.levels.clock.op m p).ratio.parent o=0 → M.turn∈Q → o∈ M.crest → Along B H N p m A o Q D (Complex.ofReal ∘ M.cicada) (MergeProof.prose M) (entry M) 0 0 (x*load M) (x*load M) (2*load M)
section
variable {T: Three G (C.path.S.side (m+1) p)}
variable (h:C.Makes) (hp:Plated (C.labels.level d) C.path (C.localSection d) C.params m N p D x) (hO:(C.path.levels.clock.op m p).ratio.parent K=0)
    (hm:m<N) (hx:SoundDoor (C.path.levels.clock.op m p) D)(hs:0≤x)
local notation "Z"=> fun i=> Along (P d) C.path N p m C.params K i D
include h hp hO hm hx hs
set_option maxHeartbeats 660000 in
lemma servedAt (hT: Useful (X) T)(hf:Blade (X) K T.snd.1 (profile ((X).activities) T.snd.2) 0 a):∃ q:Set Wing,q.Finite ∧ Along (P d) C.path N p m C.params K q D T.1 T.2.1 (profile (X).activities T.2.2) 0 0 (x*a) (x*a) (2*a):=by
    obtain ⟨I,i,M,r,H⟩:=hf; let q:Set Wing := Set.range fun i=> (M i).turn; let f(i):= r i • (Complex.ofReal ∘ (M i).cicada)
    have hy:= h.wilson.represents N p (m+1) hm; have hQ(i):=(M i|>.sells hy.good).1
    have hz: T.1= ∑ i,f i:=by rw [← hT.read,H.display hy.good.labels hT.normK,zero_smul,zero_add]
    refine ⟨q, Set.finite_range _,?_⟩; cases isEmpty_or_nonempty I; swap
    · have hP(i) := swingEye (hp.buys K q (M i) hO ⟨i,rfl⟩ (H.sit i)) (r i) ((hQ i).integrable _).ofReal
      have ht': Dominated f:=by choose y hx using fun i=> (hQ i).2; refine ⟨fun i=>‖r i‖*y i,Summable.of_finite,fun i U=>?_⟩; unfold f; simp only [Pi.smul_apply,norm_smul,Complex.norm_real,comp_apply]; exact mul_le_mul_of_nonneg_left (hx i _) (norm_nonneg _)
      let x₂ i:= r i • MergeProof.prose (M i); let y i:= r i • entry (M i); have hs0: T.snd.1= ∑ i,x₂ i:=H.lit.trans (zero_add _)
      have hk:= along_additive (P d) C.path N p m C.params K q D hx h.wilson hm.le (f:=f) hP (φ:=T.2.1) (ψ:=profile (X).activities T.snd.2) (fun U=>by rw [hs0]; simp only [Finset.sum_apply]; exact hasSum_fintype _) (fun j U=> by rw [H.run]; simp only [Finset.sum_apply]; exact hasSum_fintype _) hasSum_zero ht' (fun i=> (Complex.continuous_ofReal.measurable.comp (hQ i).1).const_smul _) (Summable.of_finite) (Summable.of_finite) (Summable.of_finite) (Summable.of_finite)
      have hf' : (fun V=>∑' i,f i V)= T.1:=by rw [hz]; funext V; simp_rw [tsum_fintype,Finset.sum_apply]
      rw [hf',tsum_zero,tsum_fintype,tsum_fintype] at hk
      have he': ∑ i,‖r i‖*(x* load (M i))≤x*a:=by simp_rw [mul_left_comm _ x,← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left H.pay hs
      have he:∑ i,‖r i‖*(2*load (M i))≤2*a:=by simp_rw [mul_left_comm _ (2:ℝ), ← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left H.pay zero_le_two
      exact hk.weaken he' he' he
    have hA:0≤ a:=by simpa using H.pay
    rw [H.run, H.lit,hz]; simp_rw [Finset.sum_of_isEmpty]; rw [add_zero]; exact empty_mark (P d) C.path N p m C.params K q D (mul_nonneg hs hA) (mul_nonneg zero_le_two hA)
lemma peppers (hT: Useful (X) T)(hf:Blade (X) K T.snd.1 (profile ((X).activities) T.snd.2) 0 a)(ha:0 ≤ a) :
    ∃ Q:Coefficient (ξ d) (C.side m p), Q.Format 0 C.params Y ∧ Q.remBound 0 Y (kappa C.path m) (x*a) ∧ (ξ d).coeffSize Q.x ≤ x*a ∧ Ride Ω K 0 D (↑((L).val)^d) T (Address.invoice Q 0 (P d) Y) ((x+2)*a):=by
    obtain ⟨q,hq,Q,hv,hR⟩:= servedAt h hp hO hm hx hs hT hf
    have hκ:0≤x*a:=mul_nonneg hs ha
    have he:x*a ≤ (x+2)*a:=by linarith only [hs,ha]
    refine ⟨Q,hv.format,hv.bound,?_,⟨hT, Useful.invoice _ _ _ _ (h.wilson.represents N p m hm.le).good hv.bound hv.format, ⟨q,hq,0,(by rw [norm_zero];exact hκ.trans he), hR.climb le_rfl (by nlinarith only [he,hκ]) he⟩,hv.agrees⟩⟩
    exact (le_mul_of_one_le_left (Work.G08.size_nonneg ..) (orbitCost_one_le _)).trans (by simpa only [sub_zero] using hv.leadP)
end
end YM.RG05Readout.Address
