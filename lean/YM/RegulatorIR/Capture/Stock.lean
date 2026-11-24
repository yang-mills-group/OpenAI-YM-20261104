import YM.RegulatorIR.Sources.Hive

/-!
# Capture horizon zero on the cover; finite matrix stock

On any bounded center cube a rooted profile-dependent packet belongs to
finite rank planes of *packets* (not just frame addresses), with plane rank
here dimension/cutoff-dependent. Makes integration and marking linearity on
every such domain exact coefficientwise. No claim full positive-output
RG dictionary supplied. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Capture
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Sources Centered Labels Source Aperture
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W I J X Y A B: Type}{q u b p a i j e k d m r:ℕ}{M: W→ℕ}{n:Page M→Side}{L:Meter W}{D:Choice M}

section Product
-- finite Leibniz. no tsum here
lemma accords (s t:ℝ)(T: Packet X i)(S:Packet X j): joined (s • T) (t • S)= (s*t) • joined T S:=by
 rw [joined,joined,← scaleSym];apply congr_arg Packet.symmetry; ext1 x; change s*_*(t*_)=_*(T _*S _);ring
lemma accordsL (T U: Orders X)(s t:ℝ) : accord (s • T) (t • U)= (s*t) • accord T U:=by
 ext1 i;ext1 j;change (∑ v∈_, crisp _ _ _)=(s*t) • _;unfold accord; rw [Finset.smul_sum]; apply sum_congr rfl;intro v _; unfold crisp;rw [Finset.smul_sum];apply sum_congr rfl;intro w hv; rw [← Finset.mem_antidiagonal.mp hv]; simp only [pie];exact accords ..
lemma pushL (T U V:Orders X): accord (T+U) V=accord T V+accord U V:=by
 have he:=accord_subL (T+U) U V; rw [add_sub_cancel_right] at he
 rw [he];abel
lemma pushR (T U V:Orders X): accord T (U+V)=accord T U+accord T V:=by
 have he:=accord_subR T (U+V) V; rw [add_sub_cancel_right] at he
 rw [he];abel
lemma accordSigma (x:Finset I)(y:Finset J)(T:I→Orders X)(V:J→Orders X): accord (∑ i∈x,T i) (∑ i∈y,V i)=∑ p∈x×ˢ y,accord (T p.1) (V p.2):=by
 have hp(P: Orders X): accord P (∑ i∈y,V i)= ∑ i∈y,accord P (V i):=by
    induction y using Finset.induction_on with
    | empty=>rw [sum_empty,sum_empty,← sub_self (0:Orders X),accord_subR];simp
    | insert i y hi ih=> rw [sum_insert hi,sum_insert hi,pushR,ih]
 rw [Finset.sum_product]; induction x using Finset.induction_on with
 | empty=>rw [sum_empty,sum_empty,← sub_self (0:Orders X),accord_subL];simp
 | insert i x hi ih=> rw [sum_insert hi,sum_insert hi,pushL,hp,ih]
end Product

structure Store (R : Room→Orders X)(Y:Set Room)(p:ℕ) where
  L : Type
  topP : Finset L
  leg : L → Orders X
  feel : L → Room → ℝ
  kept i : i∈topP → Continuous (feel i)
  sure i : i∈topP→ Cluster.Bill (leg i) p
  sense (x) : x∈Y → ∀ (e:ℕ), e ≤ p → R x e=(∑ i∈topP, feel i x • leg i) e -- remove hx
namespace Store
variable {R Q:Room→Orders X} {Y : Set Room}(s:Store R Y p)(t: Store Q Y p)

def products : Store (fun x=>accord (R x) (Q x)) Y p:= {
 L:= s.L × t.L, topP:= s.topP×ˢt.topP, leg:=fun x=> accord (s.leg x.1) (t.leg x.2), feel:=fun x y=>s.feel x.1 y*t.feel x.2 y,kept:=fun i hi=> (s.kept _ (mem_product.mp hi).1).mul (t.kept _ (mem_product.mp hi).2), sure:=fun i hi=>parent _ _ (s.sure _ (mem_product.mp hi).1) (t.sure _ (mem_product.mp hi).2), sense:=fun x h e hv=>by
    let a:=∑ i∈s.topP,s.feel i x • s.leg i;let b:=∑ i∈t.topP,t.feel i x • t.leg i
    change accord _ _ _= _
    rw [show accord (R x) (Q x) e= accord a b e from ?_]; swap
    · ext1 i;unfold accord; apply sum_congr rfl; intro j hj;have hh:= Finset.mem_antidiagonal.mp hj
      rw [s.sense x h j.1 (by omega), t.sense x h j.2 (by omega)]
    unfold a b;rw [accordSigma]; simp_rw [accordsL] }
variable {S:Heir n G} {T:S.Accounts}

def comes {R:Room→ Orders (Foot G)} (s:Store R Y p)(B:Milieu S T k p L)(w:Flap M)(m:ℕ): Store (fun x=>(S.frames w).each m (T.bulk w.prev) (R x)) Y p:={ s with
 leg:= fun x=> (S.frames w).each m (T.bulk w.prev) (s.leg x), sure:= fun i hi=> estimateM B w (s.sure i hi), sense:= fun x h i hi=> by
    rw [survivesP _ _ (s.sense _ h) hi,dividends B w s.topP (fun i=> s.feel i x • s.leg i) (fun i hi=> scalePrice (s.sure i hi) _) hi, Finset.sum_apply]; apply sum_congr rfl; intro i hi; rw [homogenous] }
variable {Z : (portraitR T).Report m}
lemma flow (B:Milieu S T k p L)(h: ∀ w, Nonempty (Store (fun x=> Z.main (Page.opening (signM M) (w,x))) Y p)) : ∀ w,Nonempty (Store (fun x=> Z.main (leafX w x)) Y p):=by refine Page.proves h ?_; intro w he; rw [show (fun x=>Z.main (leafX w.next x))= (fun x=>(S.frames w).each m (T.bulk w.prev) (Z.main (leafX w.prev x))) from funext fun x=>(Z.step_m (turnX w x)).symm]; exact ⟨he.some.comes B w m⟩
end Store

variable {S:Heir n G} (R:Reel S)(T:S.Accounts)
variable {F:Labels.Frame G d}{H:Hol G} (Z: Fabric R F H)(Φ: W→ PhaseTests d){g:ℝ}
lemma fits (w): Nonempty (Store (fun x=> Z.drawnU w x (Φ w)) (Metric.closedBall 0 g) p):=by
 let φ:=Φ w;let Q:= Address.census (S.ε w) (φ.radius+g) 0
 let A:= shape Z.A Z.origin Z.can (Z.tap w) (Z.accent w)
 let v(x:Cover × Stroke F):= A x.2 x.1
 let f(t: Cover × Stroke F)(x:Room):= framing φ (S.ε w) x t.1 t.2; have he:0<S.ε w:= S.hl _
 refine ⟨{ L:=Cover × Stroke F,topP:=Q ×ˢ Finset.univ, leg:=v, feel:=f,kept:=fun i _=>continuous_const.mul ((slope_ap i.2 (S.ε w) φ.smooth).comp (continuous_const.sub continuous_id)),sure:=fun i _ a _ b=> Prim.bound_cost ((stamp_symbol (landed Z.A Z.origin Z.can (Z.tap w) (Z.accent w) i.2 i.1)).choose_spec.1.canopy a b), sense:=fun x h a ha=>?_ }⟩ -- order helper
 change (∑ z∈Address.census _ _ x, ∑ i:Stroke F,partV _ _ _ _ _ _ _ _ z i) a= _ -- too many infer
 rw [Finset.sum_product]
 apply congr_arg (fun t:Orders (Foot G)=>t a)
 apply Finset.sum_subset
 · intro y hy; have hp:= (Address.enroll _ he φ.radius x y).mp hy; exact (Address.enroll _ he _ _ _).mpr ((dist_triangle _ x 0).trans (add_le_add hp h))
 intro y _ hv; apply sum_eq_zero; intro i _
 have hz: waveA i (S.ε w) φ.phi (slide (S.ε w) y-x)=0:=by
    by_contra! hm;apply hv; apply (Address.enroll _ he _ _ _).mpr; have hh:= φ.uses (in_ap i _ _ hm); change dist _ _ ≤ _ at hh; rwa [dist_eq_norm,sub_zero] at hh
 change f (y,i) x • v (y,i)= _; unfold f framing; rw [hz,mul_zero,zero_smul]

section
variable {m:I→ℕ}{Q: ∀ i,(portraitR T).Report (m i)} {Y:Set Room}(J:Composite I)
lemma mighty (w:W)(h:∀ i,J.In i→ Nonempty (Store (fun x=> (Q i).main (Page.opening _ (w,x))) Y p)): Nonempty (Store (fun x=>(principal J Q).main (Page.opening _ (w,x))) Y p):=by induction J with
 | atom i=> exact h i rfl
 | pair A B ih ih'=> exact ⟨(ih (fun i hi=>h i (Or.inl hi))).some.products (ih' (fun i hi=> h i (Or.inr hi))).some⟩
end
end YM.RegulatorIR.Capture
