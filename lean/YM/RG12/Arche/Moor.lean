import YM.RG12.Arche.Floored
/-!
# Uniform normalized k-column Gram, nonredundant inverse and capture reading (`ReadingAt`)
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Arche
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open MergeProof Analysis Next.UVStress Climb Ward MergeProof.East
variable {G:Gauge}{C:Family G}{ϕ : Filter UVIndex}[ϕ.NeBot] {M:∀ d, ℕ→RepChart C d}
  {d e n D k N p m:ℕ}
  {ι:Type}[Fintype ι] {W:Bid.Worth}{u ψ β δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→MergeProof.GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (P:ι → Tapes.Panel D) (B:Binding C)(H:C.Makes)(h:G.Simple)(hp:Scrim C W u ψ β δ (fly C.path.levels) r L) (O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels
local notation "F!"=> standard C
variable (z:ℝ) (hZ : ∀ i≤D,MergeProof.Accent.generator G i≤ z) (index:ι)
set_option quotPrecheck false
local notation "a!"=> (P index).arc
local notation "κ" k:max=> C.S.a k
variable {S : Table C.book} {f: Extraction.Order}(F:Final C f S) (ax:Axis)
open YM.RG12.Desk.Paired Shapes Maxwell

-- Actual RF square, exact length
def here d N n (t:ℝ) := sampleForm F (scope ax N) d (t*n)
lemma equals (v w:S.Field d) (N:ℕ)(s:ℝ) : gramEntry F d (configs (scope ax N) s 0) ax v w = illumination _ F.room.kernel.spin d d ax N s v w:=by
    rw [formula]; change _= paired _ d d _ v _; rw [pair_at]; rfl
lemma counted d (v:S.Field d) (N n:ℕ)(s:ℝ) : (here F ax d N n s).eval v=(illumination _ F.room.kernel.spin d d ax N (s*n) v v).re:=by
    change (sampleForm _ _ d _).eval v=_; unfold sampleForm; simp only [Fintype.sum_unique]; change (Frames.Gram.fromSesqui ((1:ℂ) • gramEntry F d (configs (scope ax N) _ 0) ax)).eval v=_
    rw [one_smul]; exact congr_arg Complex.re (equals F ax ..)

lemma hat_crown (C:Family G) (h:G.Simple) (b c e:ℝ) (i:ℕ) : ∀ᶠ k in atTop,
   let A':=C.path.levels; let H:= A'.clock.monitor k; c*(H^i) * (mag A' b k)^i * e ≤ A'.clock.hatBeta k:=by
  let A':= C.path.levels; let x:= A'.clock.hatBeta;let H:= A'.clock.monitor
  let B:ℝ:= i+b*i
  have hf:=tendsto_atTop_mono (fun i:ℕ => (le_refl (x i))) (hat_grows (C:=C) h)
  filter_upwards [hf.eventually (YM.Vac.Numbers.cost B (1/2) (by norm_num)),hf.eventually_ge_atTop ((c*e)^2),hf.eventually_ge_atTop 1] with k he hi hk
  change c*(H k)^i*(mag A' b k)^i*e ≤ _
  have hn : H k≥ 1:=Real.one_le_exp (sq_nonneg _)
  have hm: 0 < H k := zero_lt_one.trans_le hn
  have hx: 0<x k:= zero_lt_one.trans_le hk
  change (H k)^B≤ x k^(1/2:ℝ) at he
  have hW: (H k)^B=(H k)^i*(mag A' b k)^i:=by
     unfold B mag; rw [Real.rpow_add hm,Real.rpow_mul hm.le, Real.rpow_natCast, Real.rpow_natCast]
  by_cases ho:0 ≤ c*e
  · suffices c*e*(H k)^B ≤ x k by rw [hW] at this; linarith only [this]
    apply (mul_le_mul_of_nonneg_left he ho).trans
    rw [← Real.sqrt_eq_rpow]
    have := Real.sq_sqrt hx.le; nlinarith [Real.sqrt_nonneg (x k), show 0≤ c*e from ho]
  have hT:=mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ho) (Real.rpow_nonneg hm.le B); rw [hW] at hT;linarith only [hT,hk]
-- basic conversion by equivalences. include bounds for quotient etc. allow requested M.
structure Exchange (C:Family G)(d:ℕ)(X: Type)[NormedAddCommGroup X][NormedSpace ℂ X] where
   point: X →ₗ[ℂ] C.label d
   level : ℝ
   size : 1 ≤ level
   bill (v:X): mass C d (point v) ≤ level*‖v‖
   base (v:X): ‖v‖ ≤ level * ‖(Cells.standard C).project d (point v)‖
   outer (v:C.label d): ‖(Cells.standard C).project d v‖ ≤ level*mass C d v
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℂ X]
-- issue from equiv to the *free* physical horizon
lemma banked [FiniteDimensional ℂ X] (V: X ≃ₗ[ℂ] (F!).Field d) : Nonempty (Exchange C d X):=by
  let D:C.label d →ₗ[ℂ] (F!).Field d := (F!).project _
  let W: X →ₗ[ℂ] C.label d := ((F!).representative _).comp V.toLinearMap
  let q:= (((C.labels.level d).extra+1 :ℕ):ℝ)
  let R:= q * ‖LinearMap.toContinuousLinearMap W‖; let B':=V.symm.toContinuousLinearEquiv; let r:= ‖B'.toContinuousLinearMap‖
  let T:= ‖LinearMap.toContinuousLinearMap D‖; let S:= 1+R+r+T; have hR:0≤R:=by unfold R q; positivity
  have hr:0≤r:=(norm_nonneg (B'.toContinuousLinearMap)); have hT:0≤T:=norm_nonneg (LinearMap.toContinuousLinearMap D)
  have he:1≤S:=by unfold S; linarith
  refine ⟨W,S,he,fun v => ?_, fun v=> ?_,fun v=> ?_⟩
  · apply (mass_le_norm _ _ _).trans
    change q*‖W v‖ ≤ _
    refine (mul_le_mul_of_nonneg_left ((LinearMap.toContinuousLinearMap W).le_opNorm _) (by unfold q; positivity)).trans ?_; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (by change R≤S; unfold S;linarith) (norm_nonneg _)
  · have hw: D (W v)=V v:= (F!).rep ..; change ‖v‖ ≤ _*‖D (W v)‖; rw [hw]; exact (show _ ≤ r*‖V v‖ from by have hx:=B'.toContinuousLinearMap.le_opNorm (V v); simpa [B',r] using hx).trans (mul_le_mul_of_nonneg_right (by unfold S; linarith) (norm_nonneg _))
  exact ((LinearMap.toContinuousLinearMap D).le_opNorm _).trans (mul_le_mul (show T ≤ S by unfold S; linarith) (norm_le_mass _ _ _) (norm_nonneg _) (zero_le_one.trans he))

variable (B₀:Exchange C D X)(hQ:Observing C H ϕ M)(hb:ϕ ≤ f.fuse) (n₀:ℕ)(h₀:0 < n₀)(hn:2≤n)
include F B₀ hQ hb h₀ H h hp hZ hn
set_option maxHeartbeats 500000 in
lemma docked (minN:ℕ) : ∃ c K:ℝ,∃ N > minN, 0<c ∧ 1 ≤ K ∧ ∀ᶠ k in atTop,∀ T: ℕ→ℕ→TableL C D, Poised P B H O J n z k T →
    let μ:=mag A a! k; let p:= here F ax D N n₀ (lamp C N k μ); let W:= engineering (S:=S) M D k; let r:= (A).clock.hatBeta k
    ∃ Y:Module.End ℂ (C.label D), (∀ v,mass C D (Y v) ≤ r* mass C D v) ∧ (∀ v : C.label D,p.eval (W v) ≤ K * (mass C D v)^2) ∧
      (∀ v:X,mass C D (Y (B₀.point v)) ≤ r^2*‖v‖ ∧ c*‖v‖^2 ≤ p.eval (W (Y (B₀.point v))) ∧ p.eval (W (Y (B₀.point v))) ≤ K*‖v‖^2):=by
   obtain ⟨c,K,hc,hK,h₁⟩:=worthwhile C.labels D ax (P:=(n₀:ℝ)) (Nat.one_le_cast.mpr h₀)
   obtain ⟨N,hN,hl⟩:= (h₁.and (eventually_gt_atTop minN)).exists -- order swap hN=prop
   have hx:= hN _ (Set.mem_Icc.mpr (show 1≤ (n₀:ℝ) ∧ (n₀:ℝ) ≤ n₀ from ⟨Nat.one_le_cast.mpr h₀,le_rfl⟩))
   let l := Ultrafilter.of ϕ
   have hk': (l:Filter UVIndex) ≤ ϕ:= Ultrafilter.of_le ϕ
   obtain ⟨δ,hd,hD⟩:= fixed_shapes (l:=(l:Filter UVIndex)) P B H h hp O J z hZ index F hQ hb ax n₀ N ((Nat.zero_le _).trans_lt hl) h₀ hn
   have hage:0<a! := by have he:=(P index).huge; linarith [Nat.cast_nonneg (α:=ℝ) D]
   let G0(v:(F!).Field D):=(polished C.labels D D ax (N:ℝ)⁻¹ n₀ v v).re
   let W := B₀.level; let X₀ := (2:ℝ)^D*(3/2)
   have hw:1≤ W:=B₀.size; have hw':0<W:=zero_lt_one.trans_le hw
   have hy:0 ≤ X₀:=by unfold X₀; positivity
   let V:= K*W^2+1; have Hv:0 ≤ V:=by unfold V; positivity
   let c':= (c / W^2)/2; have hc' :0 < c':=by unfold c'; positivity
   refine ⟨c', max 1 (max (V*X₀^2) (V*W^2)),N,hl,hc',le_max_left ..,?_⟩
   have ht:Tendsto (fun k=>δ * Ship.budget (A) n k) atTop (𝓝 0):=by simpa only [mul_zero] using (Ship.diminishes (A) n h (by omega)).const_mul δ
   filter_upwards [hD,(Station.mag_rate (A) h hage).eventually_ge_atTop 1,
     hat_crown C h a! 2 (2^D) D, ht.eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num)),
     ht.eventually (ge_mem_nhds (show 0<(c' / W^2) by positivity)), (hat_grows (C:=C) h).eventually_ge_atTop W] with k hk hi hh hx' ht hK' T hT μ p' W' r
   choose Z hZ' using compare_in hQ hT.early hT.charts μ hi l hk'
   let m:= Fin.last D; let Y:= Z m
   let Q:= glowH (S:=S) M k Y
   have hZ':Comparer (ϕ:=ϕ) (hC:=H) (l:Filter UVIndex) k D T μ Z:=hZ'
   have hPrice(q:C.label D):mass C D (Y q) ≤ r*mass C D q:= by
     have he:= hZ'.ceiling m q
     let U:= (A).clock.monitor k
     change _ ≤ 2*(2*U)^D*μ^D*_ at he
     apply he.trans; apply mul_le_mul_of_nonneg_right _ (mass_nonneg ..)
     rw [mul_pow]; change 2*(2^D*U^D)*μ^D ≤ _; dsimp only at hh; change 2*U^D * μ^D * 2^D ≤ _ at hh; linarith only [hh]
   have hCost(a:C.label D) : |p'.eval (Q a)-G0 ((F!).project D a)| ≤ δ*Ship.budget A n k * mass C D a^2:=by
      rw [show p'.eval (Q a) = _ from counted F ax D (Q a) N n₀ (lamp C N k μ),← Complex.sub_re]
      refine (Complex.abs_re_le_norm _).trans (le_trans ?_ (le_of_eq (show δ*Ship.budget A n k*mass C D a*mass C D a= _ by ring)))
      exact hk T hT Z hZ' m m a a
   have hf(a:C.label D): p'.eval (W' (Y a))=p'.eval (Q a):=by
      apply congr_arg
      rw [engineering_at]; exact (map_smul ..).symm
   have hHigh(a:C.label D): p'.eval (Q a) ≤ V * mass C D a^2:=by
      have he:= (abs_le.mp (hCost a)).2; have ht : G0 ((F!).project D a) ≤ K*(W*mass _ _ a)^2:=
        (hx _).2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (B₀.outer a) _) (zero_le_one.trans hK))
      unfold V; nlinarith only [he,ht,mul_le_mul_of_nonneg_right hx' (sq_nonneg (mass C D a))]
   refine ⟨Y,hPrice,?_,?_⟩
   · intro v; obtain ⟨a,rfl⟩:= (produced hZ' m).2 v; let q:= mass C D (Z m a); have hh:= hHigh a; have ht:= mass_nonneg C D a; have hv : mass C D a ≤ X₀*q:= hZ'.base m a
     change p'.eval (W' (Y a)) ≤ _; rw [hf]
     apply hh.trans; apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht hv 2) Hv)
     rw [mul_pow,← mul_assoc]; exact mul_le_mul_of_nonneg_right ((le_max_left ..).trans (le_max_right ..)) (sq_nonneg _)
   intro a
   have hh:= B₀.bill a; have ha : 0≤r:= zero_le_one.trans (hw.trans hK')
   let i:= B₀.point a; let X':=(F!).project D i
   refine ⟨(hPrice _).trans (le_trans (mul_le_mul_of_nonneg_left hh ha) ?_),?_,?_⟩
   · rw [sq, mul_assoc]; gcongr
   · change _ ≤ p'.eval (W' (Y i)); rw [hf]; have he:= (abs_le.mp (hCost i)).1
     have hg : c/W^2 *‖a‖^2 ≤ G0 X':= by
        have he: ‖a‖^2≤ W^2*‖X'‖^2:=by rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (B₀.base _) _
        rw [div_mul_eq_mul_div,div_le_iff₀ (pow_pos hw' _)]
        have hX:c*‖X'‖^2≤G0 X':=(hx X').1
        nlinarith only [mul_le_mul_of_nonneg_left he hc.le, mul_le_mul_of_nonneg_left hX (sq_nonneg W)]
     have hr: δ * Ship.budget A n k * mass C D i ^ 2 ≤ c'*‖a‖^2:= (mul_le_mul ht (pow_le_pow_left₀ (mass_nonneg ..) hh _) (sq_nonneg _) (by positivity)).trans_eq (by change c'/W^2*(W*‖a‖)^2 = _; field_simp)
     change -(δ*_*_) ≤ p'.eval (Q i)-G0 X' at he; unfold c' at *; linarith only [hg,hr,he]
   change p'.eval (W' (Y i)) ≤ _; rw [hf]; apply (hHigh i).trans
   apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mass_nonneg ..) hh _) Hv)
   rw [mul_pow,← mul_assoc]; exact mul_le_mul_of_nonneg_right ((le_max_right ..).trans (le_max_right ..)) (sq_nonneg _)
omit F B₀ hQ hb h₀ H h hp hZ hn [ϕ.NeBot] in
lemma lip_ends (C : Family G)(N:ℕ)(hN:0 < N)(b:ℝ)(hb:0<b)(hG:G.Simple): -- ax not used delete
    Tendsto (fun k=>lamp C N k (mag (C.path.levels) b k)) atTop (𝓝 0) ∧ ∀ᶠ k:ℕ in atTop,
      C.S.a k ≤ lamp C N k (mag (C.path.levels) b k) ∧ lamp C N k (mag (C.path.levels) b k) ≤ C.S.a k * (C.path.levels.clock.hatBeta k)^2:=by
  let μ(k):ℝ:=mag (C.path.levels) b k
  have hx:= Next.Rank.Station.mag_rate C.path.levels hG hb; let Y:= C.path.levels.clock.hatBeta
  have Hk:=hat_grows (C:=C) hG
  have hr: ∀ᶠ k in atTop, μ k ≤ Y k:= (Hk.eventually (YM.Vac.Numbers.cost b 1 zero_lt_one)).mono fun k hk=> by rw [Real.rpow_one] at hk; exact hk
  have hA(k):0≤C.S.a k:=(C.S.a_pos k).le
  have ht: ∀ᶠ k : ℕ in atTop, μ k ≥ 1 ∧ ticks N (μ k)∈Set.Icc (μ k) (2*μ k) := by
     filter_upwards [hx.eventually_ge_atTop (N:ℝ)] with k hk
     have hN':1 ≤ (N:ℝ):=Nat.one_le_cast.mpr hN
     have hh : 1 ≤ μ k:=hN'.trans hk; have hv := zero_lt_one.trans_le hh
     have hu:=ticketed N (μ k) hv hN
     refine ⟨hh,(le_div_iff₀ hv).mp hu.1 |> (fun v=>by simpa using v),(div_le_iff₀ hv).mp ?_⟩
     exact hu.2.trans (by linarith [div_le_one hv|>.mpr hk])
  constructor
  · apply squeeze_zero' (g:=fun k=>2 * Station.gap C.path.levels b k) (Eventually.of_forall fun k=> show 0≤lamp C N k (μ k) from mul_nonneg (hA _) (by unfold ticks; positivity))
    · filter_upwards [ht] with i hi; unfold lamp gap; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hi.2.2 (hA _)
    simpa using (Station.gap_rate (C.path.levels) hG b).const_mul 2
  filter_upwards [ht,hr,Hk.eventually_ge_atTop 2] with k hk hh he
  exact ⟨le_mul_of_one_le_right (hA k) (hk.1.trans hk.2.1),mul_le_mul_of_nonneg_left (hk.2.2.trans (by change 2*μ k ≤ Y k^2; nlinarith)) (hA _)⟩

omit [NormedAddCommGroup X] [NormedSpace ℂ X] B₀ in
/-- Full local capture price pair at one log-separated radius per eligible level. Independent
basis chosen by the existing physical Prescription; map to free horizon entirely arbitrary here,
not used for comparing different k. Scope ax & N stay fixed. Shortfall to `FramesInput`:
need all levels and controlled costs *between* these & elsewhere. N might be large but fixed.
-/
theorem principal (Q:OPE.Prescription F.sector.derivatives)(hCo:Q.Coherent)(minN:ℕ):
    ∃ (N:ℕ), minN < N ∧ let μ(k):=mag A a! k; let t(k):= lamp C N k (μ k)
      Tendsto t atTop (𝓝 0) ∧ ∃ (c K:ℝ),0<c∧1≤K∧
      ∀ᶠ k:ℕ in atTop, C.S.a k ≤ t k ∧ t k ≤ C.S.a k * ((A).clock.hatBeta k)^2 ∧
      ((∃ T:ℕ→ℕ→TableL C D, Poised P B H O J n z k T)→
        let V:=Frames.Col (Desk.Sector F.sector.derivatives D); let X:= engineering (S:=S) M D k; let gamma:= (here F ax D N n₀ (t k)).eval
        ∃ Y: V→ₗ[ℂ] C.label D, Nonempty (ReadingAt C S D (Desk.Sector F.sector.derivatives D) (fun x=> Real.sqrt (gamma x)) k M Y 2) ∧
          (∀ v:V, c*‖v‖^2 ≤ gamma (X (Y v))) ∧ ∀ v:C.label D,gamma (X v) ≤ K* mass C D v^2):=by
   have hG:=h
   let X:=Desk.Sector F.sector.derivatives D; let V:= Frames.Col X
   obtain ⟨_, hi⟩:= F.phase.transport.comparator
   obtain ⟨Z,-,_⟩:=hi D
   obtain ⟨E⟩:= banked (C:=C) (Desk.official Q hCo D |>.trans Z) -- V tower
   have hg:0<a! := by have he:=(P index).huge; linarith [Nat.cast_nonneg (α:=ℝ) D]
   obtain ⟨c,K,N,hN,hc,hK,hT⟩:=docked P B H hG hp O J z hZ index F ax E hQ hb n₀ h₀ hn minN
   obtain ⟨hs,hL⟩:= lip_ends C N ((Nat.zero_le _).trans_lt hN) _ hg hG
   refine ⟨N,hN,hs,c,K,hc,hK,?_⟩
   have hv:= hat_grows (C:=C) hG
   filter_upwards [hT,hL,hv.eventually_ge_atTop K,hv.eventually_ge_atTop (1/c)] with k hk hl ht hC
   let r:= (A).clock.hatBeta k; have hr:1 ≤ r:= hK.trans ht
   refine ⟨hl.1,hl.2,?_⟩; rintro ⟨T,hT⟩
   let g:= (here F ax D N n₀ (lamp C N k (mag A a! k))).eval; let W:= engineering (S:=S) M D k
   obtain ⟨Y,hY,hHQ,hX⟩:= hk T hT
   refine ⟨Y.comp E.point,⟨fun x=> ?_,fun x=> (hX x).1,fun x=>?_⟩,fun v=>(hX v).2.1,hHQ⟩
   · change Real.sqrt (g _)≤ _
     have hq :0≤ r^2*mass C D x:=mul_nonneg (sq_nonneg _) (mass_nonneg ..)
     apply le_trans (Real.sqrt_le_sqrt ((hHQ x).trans ?_)) ((Real.sqrt_sq hq).le)
     rw [mul_pow]; apply mul_le_mul_of_nonneg_right _ (sq_nonneg _); exact (show K ≤ r from ht).trans (by rw [←pow_mul]; exact le_self_pow₀ hr (by decide)) -- need r≤ r^2 ^2
   change _ ≤ r^2*Real.sqrt (g (W (Y (E.point x))))
   have he:= (hX x).2.1; let y:=g (W (Y (E.point x)))
   change c*‖x‖^2 ≤ y at he
   have hy:0≤y:=(mul_nonneg hc.le (sq_nonneg _)).trans he
   change _ ≤ r^2 * Real.sqrt y
   apply le_of_pow_le_pow_left₀ (n:=2) (by norm_num) (by positivity); rw [mul_pow,Real.sq_sqrt hy]
   have Hc : 1 ≤ c*r:= by linarith only [(div_le_iff₀ hc).mp hC]
   have hX: ‖x‖^2 ≤ r*y:=by nlinarith only [mul_le_mul_of_nonneg_right Hc (sq_nonneg ‖x‖),mul_le_mul_of_nonneg_left he (zero_le_one.trans hr)]
   exact hX.trans (mul_le_mul_of_nonneg_right (show r≤(r^2)^2 by rw [←pow_mul]; exact le_self_pow₀ hr (by decide)) hy)
end YM.RG12.Arche
