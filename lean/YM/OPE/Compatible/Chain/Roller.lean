import YM.OPE.Compatible.Chain.Card
/-!
# solid and infinite Feynman moments anchored
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Terp
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script Finset Metric
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent Further.FreeCovariance.KP GaussianScore Work.F06 Work.F08
local notation "M" => TypeFace 1
variable {C:KernelChoices}{r:ℕ}
abbrev tick2 (i:ℕ):Side:=⟨i+1,Nat.succ_pos i⟩
lemma born: Tendsto (fun i:ℕ=>(tick2 i).val) atTop atTop:= tendsto_add_atTop_nat _
def vein (v:Train r)(C:KernelChoices)(i j:M)(b:Cover)(n:Side)(x:Site n):= lineC (ShellRow C v) n (x,i) (x+wrap n b,j)
private lemma approxim (ε:ℝ) (he:0<ε)(v:Train r)(h:4≤r):∃ V:Row M M,Whole V∧ ∀ᶠ n:Side in comap PNat.val atTop,∀ i j:Body 1 n,‖lineC (ShellRow C v) n i j-V.acts n i j‖<ε:=by
      let l:Filter Side:= comap PNat.val atTop
      obtain ⟨d,hd,H⟩:= tree_cost C h
      obtain ⟨u,hu,h⟩:∃ u>0,d*Real.sqrt u<ε:=by
           let a:=ε/(d+1); have ha:0<a:=div_pos he (by positivity); refine ⟨a^2,pow_pos ha _,?_⟩; rw [Real.sqrt_sq ha.le]; unfold a; field_simp; nlinarith only [he]
      obtain ⟨V,hX,hV⟩:= coinage v ‹4≤r› hu (C:=C); have hB: Tendsto (fun n:Side=> d*Real.sqrt u+ aquas n *u⁻¹) l (𝓝 (d*Real.sqrt u)):= by convert (worldZ id (show Tendsto PNat.val l atTop from tendsto_comap) u⁻¹).const_add (d*Real.sqrt u) <;> simp
      refine ⟨V,hX,?_⟩; filter_upwards [hB.eventually (eventually_lt_nhds h)] with k hk i j; rw [hV,norm_sub_rev]; exact (H v u hu k i j).trans_lt hk
lemma infinite_coin (i j:M)(x:Cover)(v:Train r)(h:4 ≤ r) : ∃ d:ℝ, Tendsto (fun n:ℕ=> vein v C i j x (tick2 n) 0) atTop (𝓝 d) :=by
      apply cauchySeq_tendsto_of_complete; rw [Metric.cauchySeq_iff]; intro ε he; let s:= ε/3; have hs: 0 < s:=by unfold s; positivity
      obtain ⟨V,hV,hp⟩:= approxim s hs v h (C:=C); have he := pocket tick2 V hV born i j x 0; obtain ⟨a,ha⟩:= Metric.cauchySeq_iff.mp he.cauchy_map s hs; obtain ⟨b,hb⟩:= eventually_atTop.mp ((show Tendsto tick2 atTop _ from tendsto_comap_iff.mpr born).eventually hp)
      refine ⟨max a b,fun m hm n hn=>?_⟩; let T(k:ℕ):= V.acts (tick2 k) (0,i) (0+wrap _ x,j); have hx: dist (T m) (T n) < s:= ha m ((le_max_left ..).trans hm) n ((le_max_left ..).trans hn); have hv(k:ℕ)(hk:b ≤ k): dist (vein v C i j x (tick2 k) 0) (T k)<s:=by rw [dist_eq_norm_sub]; exact hb k hk ..
      let f(k:ℕ):= vein v C i j x (tick2 k) 0
      calc
            _ ≤ dist (f m) (T m)+ (dist (T m) (T n) + dist (T n) (f n)) := (dist_triangle (f m) (T m) (f n)).trans (add_le_add_right (dist_triangle ..) _)
            _ < s+(s+s):=by rw [dist_comm (T n)]; gcongr; exacts [hv _ ((le_max_right ..).trans hm), hv _ ((le_max_right ..).trans hn)]
            _ = ε:= by unfold s;ring
-- reference lag
noncomputable def Spill (C:KernelChoices)(v:Train r)(h:4≤r): Row M M:= fun i j x=> Classical.choose (infinite_coin (C:=C) i j x v h)
lemma guessed (v:Train r)(h:4≤r)(i j:M)(x:Cover): Tendsto (fun n:ℕ=> vein v C i j x (tick2 n) 0) atTop (𝓝 (Spill C v h i j x)):= Classical.choose_spec (infinite_coin (C:=C) i j x v h)
variable {I:Type*}{Z:I→Side}{lp:Filter I}(hz:Tendsto (fun i=>(Z i).val) lp atTop)
include hz
lemma old_coin (v:Train r)(h:4≤ r)(i j:M)(x:Cover)(u:(i:I)→ Site (Z i)):Tendsto (fun k=> vein v C i j x (Z k) (u k)) lp (𝓝 (Spill C v h i j x)):=by
      apply Metric.tendsto_nhds.mpr; intro ε he; let s:= ε/4; have hs:0<s:=by unfold s; positivity
      obtain ⟨V,hV,hp⟩:= approxim s hs v h (C:=C); let D:=V i j x; let B:= Spill C v h i j x
      have ht : dist B D ≤ s:= by refine le_of_tendsto ((guessed v h i j x).dist (pocket tick2 V hV born i j x 0)) ?_; filter_upwards [(show Tendsto tick2 atTop _ from tendsto_comap_iff.mpr born).eventually hp] with k hk ; rw [dist_eq_norm_sub]; exact (hk ..).le
      let f(k):= V.acts (Z k) (u k,i) (u k+wrap _ x,j)
      filter_upwards [Metric.tendsto_nhds.mp (pocket Z V hV hz i j x u) _ hs, (show Tendsto Z lp _ from tendsto_comap_iff.mpr hz).eventually hp] with k hv hq; have he: dist (vein v C i j x (Z k) (u k)) (f k)<s:= by rw [dist_eq_norm_sub]; exact hq ..
      rw [dist_comm B D] at ht; change dist (f k) D <s at hv; apply (dist_triangle _ (f k) B).trans_lt; rename_i zzz; unfold s at he hv hs ht; linarith only [dist_triangle (f k) D B, hv,ht,he,hs]
lemma old_fars (v:Train r)(h:4≤r)(i j:M)(u t:(i:I)→ Site (Z i))(he:Tendsto (fun i=> separation (u i) (t i)) lp atTop): Tendsto (fun k=>lineC (ShellRow C v) _ (u k,i) (t k,j)) lp (𝓝 0):=by
      apply Metric.tendsto_nhds.mpr; intro ε he'; let s:= ε/2; have hs:0<s:=by unfold s; positivity
      obtain ⟨V,hV,hp⟩:=approxim s hs v h (C:=C); filter_upwards [Metric.tendsto_nhds.mp (pocket_fars Z V hV i j u t he) _ hs, (show Tendsto Z lp _ from tendsto_comap_iff.mpr hz).eventually hp] with k hy hh; let b:=V.acts (Z k) (u k,i) (t k,j); refine (dist_triangle _ b 0).trans_lt ((add_lt_add (b:=s) ?_ hy).trans_eq (by unfold s;ring)); rw [dist_eq_norm_sub]; exact hh ..
end YM.OPE.Cascade.Terp
