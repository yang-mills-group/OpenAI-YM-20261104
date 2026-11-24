import YM.MSbar.Pole.Sew.Power
/-! Linearity and tree boundary on pullbacks and sewn graphs. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Sew.Thread
open Set Function Filter MeasureTheory Ambient Momentum Age Mellin place Symbol Radial
open scoped Topology ContDiff BigOperators Classical
variable {I : Type} [Fintype I] (T : Thread I) (R : ℝ)
variable {F G:ℂ→Cloud I}
lemma spun_add (s:ℝ) : T.spun s (F+G)=T.spun s F+T.spun s G := by
  funext z n y; unfold spun pre; have he:= Chain.linear T.left (dimension z) 1 (F z) (G z) T.chain
  rw [one_smul,one_smul] at he; change _ * Chain.term _ _ (F z+G z) _ _ _ = _; rw [he,Pi.add_apply,Pi.add_apply,mul_add]; rfl
lemma spun_zero (s:ℝ) : T.spun s 0=0 := by funext z n y; unfold spun pre; change _ * Chain.term _ _ 0 _ _ _ = 0; rw [Chain.zero]; simp
lemma integrates_zero (s μ:ℝ) : Integrates μ (T.spun s 0) = 0 := by
  rw [spun_zero]; funext z n y
  change omega n 0 y (dimension z)*_=0
  have hb : Breezes (0 : Screened I) := fun n=>Packet.zero; have hp : Texture (0:Screened I):= ⟨fun _ _ _ _=>rfl,fun _ _ _=>rfl⟩
  rw [nat_scale hb hp hb hp y 0 (dimension z) (by intro k l; simp [lifting]),zero_mul,zero_mul]
-- etc
variable {T} {Y : Finset I}
lemma additive {s:ℝ} (h : Fits T Y) {k l:ℕ} (hf : Vortex k F) (hg : Vortex l G) (hs : 0<s)
    (p : Acts (T.inputs ∪ (T.chain.reads ∪ Y)) (T.chain.reads ∪ Y) F) (q:Acts (T.inputs ∪ (T.chain.reads ∪ Y)) (T.chain.reads ∪ Y) G) (μ:ℝ) :
    Integrates μ (T.spun s (F+G)) =ᶠ[approaching] Integrates μ (T.spun s F) + Integrates μ (T.spun s G):=by
  have hh := Vortex.add (hf.mono (le_max_left k l)) (hg.mono (le_max_right k l))
  have hp:Acts (T.inputs ∪ (T.chain.reads ∪ Y)) (T.chain.reads ∪ Y) (F+G):= Eventually.mono (p:=fun z=>Shape _ _ (F z) ∧ Shape _ _ (G z)) (Filter.Eventually.and p q) fun z he=> Shape.add he.1 he.2
  filter_upwards [(joined h _ hs hh hp).statuses,(joined h _ hs hf p).statuses,(joined h _ hs hg q).statuses] with z hz hx hy
  have he : ∀ n x,T.spun s (F+G) z n x=T.spun s F z n x+T.spun s G z n x:=fun n x=>congr_fun (congr_fun (congr_fun (spun_add T s) z) n) x
  funext n x; rw [Pi.add_apply,Pi.add_apply, Pi.add_apply]; unfold Integrates
  have hv:= Ambient.aligned hx.2 hx.1 hy.2 hy.1 hz.2 hz.1 1 1 x (by intro y r; simp [lifting,he]) (dimension z)
  rw [hv,one_mul,one_mul,add_mul]

def rests (A : Finset I)(a:ℤ)(F:ℂ→Cloud I):= ∀ᶠ z in approaching,∀ n x,∃ y,Tendsto (fun s:ℝ => roll A ⟨a,0⟩ s F z n x) (𝓝[>] 0) (nhds y)

lemma term_limits {Q : ℝ → Cloud I} (Z : Chain I) (p : I) (d:ℂ) (h : ∀ n x, ∃ c : ℂ,Tendsto (fun s=>Q s n x) (𝓝[>] 0) (nhds c)) (n:ℕ)(x:External I n):∃ c : ℂ,
    Tendsto (fun s=> Chain.term p d (Q s) Z n x) (𝓝[>] 0) (nhds c):= by
  choose c hc using h
  cases Z with
  | scalar=> exact ⟨_,hc _ x⟩
  | query i=> exact ⟨_,hc _ _⟩
  | pair i j =>
    exact ⟨_,(tendsto_finsetSum Finset.univ fun l _ => hc n (joint i j x (ortho n l) (ortho n l))).add ((hc (n+1) (joint i j (place.pad n ∘ x) (place.room n 1) (place.room n 1))).const_mul (d-2*n))⟩
lemma at_zero (A:Finset I)(L:Finset I) (h:Fits T Y) (a:ℤ) (p:T.inputs⊆A) (hv:Disjoint A T.chain.reads) (hL:L⊆T.output)
    (hs:rests A a F) (hx:Acts (T.inputs∪(T.chain.reads∪Y)) (T.chain.reads∪Y) F): Wing A ⟨a+2-T.chain.demand,0⟩ (T.twig L 1 F):=by
  intro hD
  filter_upwards [hs,hx] with z hm hk n x
  let c:= T.momentum L n x; let y:= T.warp n (c,x); let Q(s:ℝ): Cloud I:=roll A ⟨a,0⟩ s F z
  obtain ⟨b,hb⟩:= term_limits (Q:=Q) T.chain T.left (dimension z) hm n y
  have hv' := ( (Filter.Tendsto.mul_const T.scalar (Heat.smooth_zero c).tendsto).mono_left (nhdsWithin_le_nhds (s:=Ioi _)) ).mul hb
  simp only [Heat.drops,zero_mul] at hv'; refine hv'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht; exact bridge_scale A h p hv _ ht x hL (fun i hi=> hk.angle i (Finset.mem_union_left _ hi))
end YM.MSbar.Pole.Sew.Thread
