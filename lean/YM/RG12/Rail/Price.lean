import YM.RG12.Rail.Wax
/-! Actual physical coercivity and tested transport on arbitrary consecutive k pairs, under
   *dosage* apertures financed on a constructor. Only requires both Poised (e.g. on broad
   interior of any stage, see GeneralRoll), for the SAME history and Final. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Rail
open Function Filter Set Finset Lattice Wilson RG Next.Rank Next.Rank.Atlas Station Prayer Perch Glimmer Real
open Extraction Bid MergeProof Source Org Spec PhysicalNext PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank.Soft
open MergeProof.East Arche Shapes Roof RG12.Frames RG12.Desk.Paired
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{ϕ : Filter UVIndex}[ϕ.NeBot] {M : ∀ d, ℕ→RepChart C d} {d n:ℕ}
 {ι:Type}[Fintype ι] {W:Bid.Worth}{u ψ β δ:ℕ→ℝ}{r:ℕ→ℕ}
open PhysicalNext.Repeat.Legato.Bandage Next.Rank.Tapes.West
variable {L:∀ N p m:ℕ,m<N→MergeProof.GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (T:ι → Tapes.Panel d) (B:Binding C)(H:C.Makes)(h:G.Simple)(hp:Scrim C W u ψ β δ (fly C.path.levels) r L) (O:HaarBudget G)(J:Precision.ChartRatio G)
set_option quotPrecheck false
local notation "A" => C.path.levels
variable (z:ℝ) (hZ : ∀ i≤d,MergeProof.Accent.generator G i ≤ z) (index:ι)
local notation "a!"=> (T index).arc
local notation "cK" k:max => (A).clock.hatBeta k
local notation "cheap" x:max k:max=> bill x (cK k)
local notation "Y$" k:max=> mag (A) a! k
variable {S : Table C.book} {f: Extraction.Order}(F:Final C f S)(hQ:Observing C H ϕ M)(hb:ϕ ≤ f.fuse)(hn:2≤n)
local notation "V!"=>Desk.Sector F.sector.derivatives d
local notation "X!"=> Frames.Col (V!)

structure Good (Z:∀ i:Fin (d+1),Module.End ℂ (C.label i))(k:ℕ) : Prop where
   pages: ∃ U:ℕ→ℕ→TableL C d,Poised T B H O J n z k U∧ Comparer (ϕ:=ϕ) (hC:=H) (Ultrafilter.of ϕ) k d U (Y$ k) Z
set_option linter.unusedSectionVars false -- duplicate auto include
include F hQ hb H h hp hZ hn
lemma available (_hs:Slugg (A))(ax:Axis)(N:ℕ)(hN:0 < N):
   ∀ᶠ k in atTop,
   ∀ (Z:∀ i:Fin (d+1),Module.End ℂ (C.label i)), Good (n:=n) (ϕ:=ϕ) T B H O J z index Z k →
    ∀ i:ℕ, let s:= atR (A) a! N i k; s∈Icc 1 ((A).clock.monitor k) → s^(2*d) ≤ cheap (cut₀ n) k → ∀ v:(X!),
      |(sampleForm F (Shapes.scope ax N) d (flareR (A) N i k)).eval ((jaw F d M k Z) (Frames.dilate s v)) - (white F d ax N v v).re| ≤ fineprint (A) n k * ‖v‖^2:=by
   obtain ⟨c,hc,hv⟩:= lightR (l:=(Ultrafilter.of ϕ:Filter UVIndex)) T B H h hp O J z hZ index F hQ hb ax N hN hn
   obtain ⟨Y₀,hG,hJ⟩:= whitened F d
   have he : 0< σ₀ n:=by unfold σ₀; have hv:(2:ℝ)≤n:=(by exact_mod_cast hn); exact inv_pos.mpr (mul_pos (by norm_num) (zero_lt_two.trans_le hv))
   have hμ:=hat_rate (A) h
   filter_upwards [hμ.eventually (transports (show -(σ₀ n)+cut₀ n< - cut₀ n from by unfold cut₀;linarith) (Y₀*c)), hv] with k hk hm Z hT i s hi hE v
   obtain ⟨U,ha,hθ⟩:=hT.pages
   let x:=flareR (A) N i k
   have hx :0 < x:=by
     unfold x flareR; refine mul_pos (C.S.a_pos _) (pos_of_mul_pos_right (show 0 < s from zero_lt_one.trans_le hi.1) ?_); exact (inv_pos.mpr (mag_pos ..)).le
   have hy:= hJ ax N k M Z (mul_nonneg hc (Ship.budget_pos ..).le) hx hi.1 (hm U ha Z hθ i hi) v
   refine hy.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
   refine (mul_le_mul_of_nonneg_left hE (mul_nonneg hG (mul_nonneg hc (Ship.budget_pos ..).le))).trans ?_
   unfold fineprint; rw [budged,← mul_assoc,mul_assoc,overlap]; exact hk

-- `at_neighbor`: dilation uses ratio of the exact *tested* lengths, no distance-round loss.
omit F hQ hb H h hp hZ hn in
lemma across_torch {Y:Levels G}(b:ℝ)(N k:ℕ)(hN:0 < N) : drift Y b N (k+1) * (torchR Y b N k / torchR Y b N (k+1))=jumped Y b N (knot N (mag Y b k)) k:=by
   unfold drift torchR atR flareR jumped atR; rw [Y.S.a_step]
   have h:0<knot N (mag Y b (k+1))*N:= (Nat.mul_pos (Nat.ceil_pos.mpr (div_pos (mag_pos ..) (Nat.cast_pos.mpr hN))) hN)
   unfold bridge; push_cast; have hq: (knot N (mag Y b (k+1)):ℝ)≠0 := (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (fun hq=> by rw [hq] at h; omega):(0:ℕ)<knot N (mag Y b (k+1))) : (0:ℝ)<_).ne'
   field_simp [hq,(mag_pos Y b (k+1)).ne',(Nat.cast_pos (α:=ℝ)|>.mpr hN).ne',(Y.S.a_pos k).ne']

def stepLense (F:Final C f S)(d:ℕ)(M:∀ d,ℕ→RepChart C d)(k:ℕ)(Z:∀ i:Fin (d+1),Module.End ℂ (C.label i))(N:ℕ)(b:ℝ):Col (Desk.Sector F.sector.derivatives d) →ₗ[ℂ] S.Field d:= jaw F d M k Z ∘ₗ Frames.dilate (drift (A) b N k)

omit hQ hb H h hp hZ hn in
private lemma plus_dilation (x:X!)(a b:ℝ): (Frames.dilate a (Frames.dilate b x))=Frames.dilate (a*b) x:=by ext1 j; rw [Frames.dilation,Frames.dilation,Frames.dilation,mul_pow]; module -- ofReal cast need simp
lemma bloc (hs:Slugg (A))(ax:Axis)(N:ℕ)(hN:0 < N):
   ∀ᶠ k in atTop, ∀ (U k₀:∀ i:Fin (d+1), Module.End ℂ (C.label i)), Good (n:=n) (ϕ:=ϕ) T B H O J z index U k → Good (n:=n) (ϕ:=ϕ) T B H O J z index k₀ (k+1) →
   ∀ x:X!, let a(i):=torchR (A) a! N i
   let R i:= (sampleForm F (Shapes.scope ax N) d (a i)).eval
   let g:=(white F d ax N x x).re; let q:=fineprint (A) n k * ‖x‖^2
   let v:=(stepLense F d M k U N a!) x; let w:=(stepLense F d M (k+1) k₀ N a!)
   let d₀:= a k / a (k+1)
   1 ≤ d₀ ∧ |R k v-g| ≤ q ∧ |R (k+1) (w x)-g| ≤ q ∧ |R k (w (Frames.dilate d₀ x))-g| ≤ q:=by
  have hc:0 < a!:=by have e:=(T index).huge; linarith [Nat.cast_nonneg (α:=ℝ) d]
  have he:= tour_clock (A) h a! hc hs N hN n d hn
  have hf:= available T B H h hp O J z hZ index F hQ hb hn hs ax N hN
  have hd : 0 ≤ cut₀ n:=by unfold cut₀ σ₀; positivity
  have hx:=bill_mono (A) h hd
  filter_upwards [he,(tendsto_add_atTop_nat 1).eventually he,hf,(tendsto_add_atTop_nat 1).eventually hf,hx] with k h1 h2 h3 h4 hg X Z hu hz x a R g q v w d₀
  let t i:= drift (A) a! N i; let δ:= jumped (A) a! N (knot N (Y$ k)) k
  have hδ: t (k+1)*d₀= δ := across_torch a! N k hN
  have hp : 1 ≤ d₀:=by
     have hV : 0 < d₀:=div_pos (flare_pos _ _ _ hN k) (flare_pos _ _ _ hN (k+1)); have h: t (k+1)*d₀ ≥ 2:= (show 2 ≤ δ from h1.2.1.1).trans_eq hδ.symm -- orientation?
     have h':t (k+1) ≤ 2:=h1.2.2.2.2; nlinarith
  refine ⟨hp,h3 X hu _ h1.1 h1.2.2.1 x,?_,?_⟩
  · have he:= h4 Z hz _ h2.1 h2.2.2.1 x
    apply he.trans; unfold q; apply mul_le_mul_of_nonneg_right _ (sq_nonneg _); unfold fineprint
    unfold bill at *; rw [mul_neg, exp_neg, mul_neg, exp_neg]; exact inv_anti₀ (exp_pos _) hg
  change |R k (jaw F d M (k+1) Z (Frames.dilate (t (k+1)) (Frames.dilate d₀ x))) - g| ≤ _
  rw [plus_dilation, hδ]
  obtain ⟨hu₁,hu₂⟩:= h1.2.1
  unfold R a torchR;rw [← hooked]
  have he:=h4 Z hz (bridge (A) k*knot N (Y$ k)) (show δ∈Set.Icc 1 _ from ⟨one_le_two.trans hu₁,hu₂⟩) h1.2.2.2.1 x
  apply he.trans; unfold q; apply mul_le_mul_of_nonneg_right _ (sq_nonneg _); unfold fineprint
  unfold bill at *; rw [mul_neg, exp_neg, mul_neg, exp_neg]; exact inv_anti₀ (exp_pos _) hg
end YM.RG12.Rail
