import YM.RegulatorIR.Cluster.Restrict

/-! At fixed array and kernel K, absolute convergence when lifting the K
support restriction. We do not evolve with cropped arrays. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Finset Function Budget Budget.Packet Budget.Layer Budget.Tuple Diagram Filter
open scoped Topology BigOperators Classical ENNReal
variable {X Y:Type}{r s:ℕ}{b c :ℝ≥0∞}

def pall (K:Layer X X) (l : Finset X) : Layer X X:= fun x y=> if x ∈ l ∧ y∈l then K x y else 0
lemma pall_row (K:Layer X X)(l:Finset X)(M:Tariff X)(h:row K M id id b) : row (pall K l) M id id b:=fun i=>le_trans (quota_dom _ _ (fun j=>by unfold pall; split_ifs; exact le_rfl; exact enorm_zero.le.trans (by positivity))) (h i)

lemma square : Tendsto (fun l:Finset X=> l ×ˢ l) atTop atTop:=by
 refine tendsto_atTop_atTop.mpr ?_
 intro v
 refine ⟨v.image Prod.fst ∪ v.image Prod.snd,fun b hb (x:X×X) hx=> mem_product.mpr ⟨hb (mem_union.mpr (Or.inl (mem_image_of_mem _ hx))),hb (mem_union.mpr (Or.inr (mem_image_of_mem _ hx)))⟩⟩
lemma loop_sums (T:Packet X (r+2)){K:Layer X X}(z:Tuple X r) (h:quota T 1≠⊤)(hp:height K c)(hc:c≠⊤): Summable (curve T K z) := by
 apply quota_summable (w:=1) (fun _=> le_rfl) (ne_top_of_le_ne_top (ENNReal.mul_ne_top hc h) ?_)
 have hz:= ENNReal.le_tsum (f:=fun x:Tuple X r=> quota (fun y:X×X=>T (linked x y)) 1) z
 simp only [quota_base] at hz
 rw [quota_base,quota_base, ← price_link (r:=r) (X:=X) (fun x=>‖T x‖ₑ)]; apply le_trans _ (mul_le_mul_right hz c)
 rw [← ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro x; rw [curve,enorm_mul]; exact mul_le_mul_left (hp ..) _

lemma loop_P (T:Packet X (r+2))(K:Layer X X)(z:Tuple X r)(l:Finset X) : loop T (pall K l) z = ∑ i∈ l×ˢ l, curve T K z i:=by
 unfold loop; rw [tsum_eq_sum (s:=l×ˢ l)]
 · apply Finset.sum_congr rfl;intro x hx;rw [curve,pall,if_pos (mem_product.mp hx)];rfl
 intro a ha; rw [curve,pall,if_neg (fun hh=> ha (mem_product.mpr hh)),zero_mul]
lemma loop_winds (T:Packet X (r+2))(K:Layer X X)(z:Tuple X r) (h:quota T 1≠⊤)(hp:height K c)(hc:c≠⊤) : Tendsto (fun l:Finset X=> loop T (pall K l) z) atTop (𝓝 (loop T K z)):=by
 simp_rw [loop_P]
 exact (loop_sums T z h hp hc).hasSum.comp square

-- simpler than splice local enough for absolute. Requires U bounded.
def Enough (T:Packet X r) : Prop:= ∃ b:ℝ≥0∞, b≠⊤ ∧ ∀ x, ‖T x‖ₑ ≤ b
lemma enough (T:Packet X r)(h: quota T 1≠⊤): Enough T :=⟨_, h, fun x=>by simpa only [Pi.one_apply,mul_one] using term_le T 1 x⟩
lemma held_enough (T:Packet X (r+1))(M:Tariff X)(h: localQ M T b)(hb:b≠⊤): Enough T:=by
 refine ⟨b,hb,fun x=>?_⟩
 apply le_trans _ (h 0 (x 0))
 apply le_trans _ (term_le (fun y:Hold 0 (x 0)=>T y.val) (fun y=>M.diameter y.val) ⟨x,rfl⟩)
 exact (mul_one (‖T x‖ₑ)).symm.le.trans (mul_le_mul_right (M.diameter_unit x) _)

def lesson (T:Packet X (r+1))(U:Packet X (s+1))(K:Layer X X)(z:Tuple X (r+s))(y:X×X):= T (Fin.cons y.1 (cutLeft z))*(K y.1 y.2*U (Fin.cons y.2 (cutRight z)))
lemma quota_lesson (T:Packet X (r+1))(U:Packet X (s+1))(K:Layer X X){M:Tariff X}(hh:row K M id id c)(h:∀ x,‖U x‖ₑ ≤ b)(z: Tuple X (r+s)): quota (lesson T U K z) 1 ≤ quota T 1*(c*b):=by
 let f : X ↪ Tuple X (r+1) := ⟨fun x=>Fin.cons x (cutLeft z),fun a d he=> Prod.mk.inj ((glueEquiv X r).injective he)|>.1⟩
 apply le_trans _ (mul_le_mul_left (quota_restrict _ f.injective T 1) _)
 rw [quota_base,ENNReal.tsum_prod']; change (∑' (i:X) (j:X), _ ) ≤ quota (T ∘ f) 1*(c*b)
 rw [quota_base,← ENNReal.tsum_mul_right]; apply ENNReal.tsum_le_tsum; intro i
 simp_rw [lesson, enorm_mul]
 rw [ENNReal.tsum_mul_left]; apply mul_le_mul_right _ (‖T (f i)‖ₑ)
 apply le_trans _ (mul_le_mul_left ((quota_mono (K i) (w:=1) (fun j=>M.unit (id i) (id j))).trans (hh i)) _)
 rw [quota_base,← ENNReal.tsum_mul_right]; exact ENNReal.tsum_le_tsum fun j=>mul_le_mul_right (h _) _
lemma knot_sums (T:Packet X (r+1))(U:Packet X (s+1)){K: Layer X X}{M:Tariff X}(h:quota T 1≠⊤)(hh: Enough U)(hk:row K M id id c)(hc:c≠⊤)(z:Tuple X (r+s)) : Summable (lesson T U K z):=by obtain ⟨b,hb,H⟩:=hh; exact quota_summable (w:=1) (fun _=>le_rfl) (ne_top_of_le_ne_top (by finiteness) (quota_lesson T U K hk H z))
lemma knot_price (T:Packet X (r+1))(U:Packet X (s+1))(K:Layer X X)(z: Tuple X (r+s))(h: Summable (lesson T U K z)): knot K T U z=∑' y,lesson T U K z y:=by
 rw [h.tsum_prod]; nth_rw 1 [← recombine z]; rw [knot,splice_at]; apply tsum_congr; intro i; rw [lace,ray,← tsum_mul_left]; apply tsum_congr; intro j
 rw [swivel,Fin.cons_zero, show update (Fin.cons i (cutRight (r:=r) z):Tuple X _) 0 j=Fin.cons j (cutRight z) from ?_]; rfl
 ext1 a; induction a using Fin.cases <;> simp
lemma knot_part (T:Packet X (r+1))(U:Packet X (s+1))(K:Layer X X)(l:Finset X) (z:Tuple X (r+s)): knot (pall K l) T U z =∑ i∈ l×ˢ l,lesson T U K z i:=by
 have h (x:X×X) (hx:x∉ l×ˢ l): lesson T U (pall K l) z x=0:=by rw [lesson,pall,if_neg (fun hh=>hx (mem_product.mpr hh)),zero_mul,mul_zero]
 rw [knot_price T U (pall K l) z (summable_of_ne_finset_zero (s:=l×ˢ l) h),tsum_eq_sum h]
 apply Finset.sum_congr rfl;intro i hi;rw [lesson,pall,if_pos (mem_product.mp hi)]; rfl
lemma knot_winds (T:Packet X (r+1))(U:Packet X (s+1)){K: Layer X X}{M:Tariff X}(h:quota T 1≠⊤)(hh:Enough U)(hk:row K M id id c)(hc:c≠⊤)(z:Tuple X (r+s)): Tendsto (fun l:Finset X=> knot (pall K l) T U z) atTop (𝓝 (knot K T U z)):=by
 have hx:= knot_sums T U h hh hk hc z
 simp_rw [knot_part,knot_price T U K z hx]; exact hx.hasSum.comp square
end YM.RegulatorIR.Cluster
