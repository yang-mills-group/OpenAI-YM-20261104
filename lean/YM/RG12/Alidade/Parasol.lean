import YM.RG12.Alidade.Settlement
import YM.RG12.Alidade.Terminal
/-! # Physical cards. All measured k, short k bridges, cross-adj pricing through
  meter errors (order zero only: genuine e^{-(logLambda)^2} etc; not claiming power-g
  residual without higher-order cancellations). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Alidade
open Function Set Filter Finset Lattice Wilson RG Source Real Frames Commission Rail
open Extraction Bid MergeProof Org Spec PhysicalNext PhysicalNext.RankCovariance PhysicalNext.InteractingRank.Soft
open MergeProof.East Arche Shapes Roof RG12.Frames RG12.Desk.Paired YM.Pert.Dense
open PhysicalNext.Repeat.Legato.Bandage Next.Rank.Tapes.West Next.Rank Next.Rank.Atlas Station Prayer Perch Glimmer
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}{d:ℕ}
local notation "Z!"=>C.path.levels
local notation "χ"=>C.path.levels.clock.hatBeta
variable (U:Final C f S) (Q:YM.OPE.Prescription U.sector.derivatives)(hQ:Q.Coherent)
variable {φ:Filter UVIndex}[φ.NeBot]{M:∀ d,ℕ→RepChart C d}
variable (P:Port C){lit:ℕ→Prop}(hP:Outbound P lit U.room.cutoff)
variable {W:Worth}{u ψ σ δ:ℕ→ℝ}{r:ℕ→ℕ}{L:∀ N p m:ℕ,m<N→MergeProof.GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (h:G.Simple)(hp:Scrim C W u ψ σ δ (fly C.path.levels) r L)(hO:Observing C U.room.cutoff φ M)(hF:φ ≤ f.fuse)
variable (i:Fin 3)(ax:Axis)
set_option quotPrecheck false
local notation "arc!"=> (P.panels d i).arc
local notation "B!"=> U.sector.derivatives
local notation "D!"=> Desk.official Q hQ d
local notation "X!"=> wheelR U d
-- pay Lens horizon reps in monitor powers (not spilling into each step, for thinned bridges)
include U P i h
lemma chooses {q:ℕ→TableL C d}(hv:∀ᶠ k in atTop,lit k→Good (ϕ:=φ) (n:=trays d) (P.panels d) P.chart U.room.cutoff P.haar P.locality (P.budget d) i (q k) k) (hs:Slugg (Z!)) (N:ℕ)(hN:0<N):
 ∃ l:ℕ, ∀ᶠ k:ℕ in atTop, let a:=arc!
    let r:= torchR (Z!) a N k; let b:=(Z!).clock.monitor k
    let Y:=stepLense U d M k (q k) N a
    (C.S.a k ≤ r ∧ r ≤ C.S.a k*b^l) ∧
    (lit k → ∀ j:Grade d, ∃ H: (X!) j→ₗ[ℂ] C.label j, (∀ v,mass C j (H v) ≤ b^l*‖v‖) ∧ ∀ v, Y (put (X!) j v)=(B!).rise j.is_le (engineering (S:=S) M j k (H v))):=by
   have he:0 < arc! := by have he:= (P.panels d i).huge; linarith [Nat.cast_nonneg (α:=ℝ) d]
   have hh:= (sitespec h hs he N hN).2
   obtain ⟨E,hE⟩:= exists_nat_gt arc!
   let l:= 1+d+E*(d+1)
   let c(j:Grade d):= ‖LinearMap.toContinuousLinearMap (code U d j)‖ * (↑((C.labels.level j).extra+1):ℝ); let z:=2^(2*d+1) * (∑ i,c i)
   have hc(j):0 ≤ c j:=by unfold c; positivity
   have hb' (j:Grade d): c j ≤ ∑ i,c i:=single_le_sum (fun i _=>hc i) (mem_univ ..)
   refine ⟨l,?_⟩
   filter_upwards [hv,hh, (monitor_late (Z!) h).eventually_ge_atTop z,(monitor_late (Z!) h).eventually_ge_atTop (2:ℝ)] with k hk hx hz hf a t b Y
   have h0:1≤ b:=(monitor_big ..)
   have ha: mag (Z!) a k ≤ b ^ E:=by rw [mag,← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le h0 hE.le
   obtain ⟨h1,h2,h3,h4⟩:=hx
   refine ⟨⟨h3,h4.trans ?_⟩,?_⟩
   · rw [mul_assoc]; refine mul_le_mul_of_nonneg_left ?_ (C.S.a_pos _).le
     change 2 ≤ b at hf
     apply (mul_le_mul hf ha (mag_pos ..).le (zero_le_one.trans h0)).trans
     rw [mul_comm b,← pow_succ]; exact pow_le_pow_right₀ h0 (by unfold l; rw [Nat.mul_add_one E d]; omega)
   intro hlo j;let t':= drift (Z!) a N k;let e:= (t'^ j.val:ℝ); let H:= (e:ℂ) • ((q k j).comp (code U d j))
   have hj: 1≤e:=one_le_pow₀ h1.1
   have he': e≤2^d:= (pow_le_pow_left₀ (zero_le_one.trans h1.1) h1.2 j.val).trans (pow_le_pow_right₀ (by norm_num) j.is_le)
   refine ⟨H,fun v=> ?_,fun v=> ?_⟩
   · have he : mass C j (code U d j v) ≤ c j*‖v‖:= by
        apply (mass_le_norm ..).trans
        unfold c; rw [mul_comm _ (↑(_:ℕ):ℝ),mul_assoc]; exact mul_le_mul_of_nonneg_left ((LinearMap.toContinuousLinearMap (code U d j)).le_opNorm v) (by positivity)
     obtain ⟨W',hW,hT⟩:=(hk hlo).pages
     let φ:=mag (Z!) a k; have h2':0≤φ:=(mag_pos ..).le
     have hu:mass C j (H v)=e*mass C j ((q k j) (code U d j v)):=labels_cost e (zero_le_one.trans hj) _
     have hm:1 ≤ (2:ℝ)*b:=one_le_mul_of_one_le_of_one_le (by norm_num) h0
     calc
      _ ≤ e*(2*(2*b)^j.val*φ^j.val*mass C j (code U d j v)):=by rw [hu]; apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hj); exact hT.ceiling j _
      _ ≤ 2^d * (2*(2*b)^d*(b^E)^d*((∑ i,c i)*‖v‖)):=by
        have h': 0 ≤ b:=zero_le_one.trans h0; have hΓ:=mass_nonneg C j (code U d j v)
        have hr:= (pow_le_pow_left₀ h2' ha j.val).trans (pow_le_pow_right₀ (one_le_pow₀ h0) j.is_le : (b^E)^j.val ≤ (b^E)^d)
        refine mul_le_mul he' (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hm j.is_le) zero_le_two) hr (pow_nonneg h2' _) (mul_nonneg zero_le_two (pow_nonneg (zero_le_one.trans hm) _))) (he.trans (mul_le_mul_of_nonneg_right (hb' j) (norm_nonneg _))) hΓ (by positivity)) (by positivity) (by positivity)
      _ = z * b^(d+E*d)*‖v‖:=by rw [pow_add,mul_pow,pow_mul]; unfold z; rw [two_mul d,pow_add,pow_one,pow_add]; ring
      _ ≤ _:=by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply (mul_le_mul_of_nonneg_right (show z ≤ b from hz) (pow_nonneg (zero_le_one.trans h0) _)).trans
        rw [mul_comm b,←pow_succ]; exact pow_le_pow_right₀ h0 (by unfold l; rw [Nat.mul_add_one E d]; omega)
   have hf : dilate t' (put (X!) j v)= put _ j ((e:ℂ) • v):=by
      ext1 j'; rw [dilation]; unfold put
      by_cases ht:j=j'
      · subst j'; rw [Pi.single_eq_same,Pi.single_eq_same]
      rw [Pi.single_eq_of_ne (Ne.symm ht),smul_zero,Pi.single_eq_of_ne (Ne.symm ht)]
   change jaw U d M k (q k) (dilate t' _)=(B!).rise j.is_le (engineering (S:=S) M j k (H v))
   rw [hf,piece,map_smul]
   have hz(w): glowH (S:=S) M k (q k j) w= engineering (S:=S) M j k ((q k j) w):=by
       change S.project _ ((_ :ℂ) • _) = (_ :ℂ) • _; simp only [map_smul]; rfl
   rw [hz,map_smul]; rfl

-- key presentation retains quantitative result and doesn't require all k LANDED
structure Club (M:∀ d,ℕ→RepChart C d)(P:Port C)(U:Final C f S)(Q:YM.OPE.Prescription U.sector.derivatives)(hq:Q.Coherent)(φ:Filter UVIndex)[φ.NeBot](k0 N:ℕ)(ax:Axis)(lit:ℕ→Prop)
  (id:Fin 3)(Z:ℕ→TableL C k0)(Y:ℕ → Col (wheelR U k0)≃ₗ[ℂ] S.Field k0)(K:ℝ)(p:ℕ):Prop where
     numbers : 0 < N ∧ 1 ≤ K
     poses : ∀ᶠ k in atTop, lit k → Good (ϕ:=φ) (n:=trays k0) (P.panels k0) P.chart U.room.cutoff P.haar P.locality (P.budget k0) id (Z k) k ∧
           (Y k).toLinearMap=stepLense U k0 M k (Z k) N (P.panels k0 id).arc
     calendar : let t:= torchR C.path.levels (P.panels k0 id).arc N
                (∀ i,0 < t i)∧∀ᶠ i:ℕ in atTop,t (i+1) ≤ t i
     active : let t:=torchR C.path.levels (P.panels k0 id).arc N
              ∀ᶠ i in atTop, lit i→ Office M U.sector.derivatives (Desk.official Q hq k0) (Y i) (lens U k0 ax N (t i)) (t i) i p K
     land : let t:= torchR C.path.levels (P.panels k0 id).arc N
            Landing C M U.sector.derivatives Y (Desk.official Q hq k0) (lens U k0 ax N ∘ t) t lit 2 K
     wears : let t:= torchR C.path.levels (P.panels k0 id).arc N
             ∀ᶠ k in atTop, lit k → lit (k+1) → let g(i):= lens U k0 ax N (t i); let r:=t k / t (k+1); let o:= 4*K*fineprint C.path.levels (trays k0) k
                     1 ≤ r ∧ ∀ v: Col (wheelR U k0), g k (Y (k+1) (Frames.dilate r v)) ≤ (1+o)* g (k+1) (Y (k+1) v) ∧ g (k+1) (Y (k+1) v) ≤ (1+o)*g k (Y (k+1) (Frames.dilate r v))
include U P i h
include hO hp hF hP
set_option maxHeartbeats 400000 in
theorem planned (Ha:Assembly U P lit M Q hQ φ) (ax:Axis)(d₀:ℕ)(hm:ℕ):∃ (N:ℕ)(Z:ℕ→TableL C d₀)(Y:ℕ → Col (wheelR U d₀)≃ₗ[ℂ] S.Field d₀)(K:ℝ)(p:ℕ), hm ≤ N∧ Club M P U Q hQ φ d₀ N ax lit i Z Y K p:=by
    let D:=d₀
    obtain ⟨Z,K,hk,hZ,hV⟩:= Ha.matrices D i ax
    obtain ⟨J,hJ,hc⟩:= cover U P hP (d:=D) h hp i hO hF ax
    obtain ⟨N₀,hN⟩:= eventually_atTop.mp (hV.and hc)
    obtain ⟨N,hδ,hF₁⟩:= Arche.principal (P.panels D) P.chart U.room.cutoff h hp P.haar P.locality _ (hP.covered.2.1 D) i U ax hO hF 1 (by norm_num) (n:=trays D) (Nat.le_add_left ..) Q hQ (max hm N₀)
    have hn:0 < N:=(Nat.zero_le _).trans_lt hδ
    obtain ⟨hz',hδ'⟩:=hN N ((le_max_right ..).trans hδ.le)
    let X:= wheelR U D
    let a:= (P.panels D i).arc
    let Y(k):=stepLense U D M k (Z k) N a; let t:=torchR C.path.levels a N
    let g(k):=lens U D ax N (t k); let D':=Desk.official Q hQ D
    have he:0 < a:=by have he:=(P.panels D i).huge; linarith only [he,Nat.cast_nonneg (α:=ℝ) D]
    have ht:∀ᶠ k in atTop,lit k→ Tests (g k ∘ Y k) K∧ triangular X (D'.symm.toLinearMap.comp (Y k)):= hz'.mono (fun k hk h=>⟨Gram.stable (hk h).2.1,(hk h).1⟩)
    have hy:∀ᶠ k in atTop,lit k→Bijective (Y k):=by
       filter_upwards [ht] with k hk h
       have H:= (hk h).1
       have hf:g k 0=0:=by simpa only [Function.comp_apply,map_zero] using! H.zero
       have hi:Injective (Y k):=LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (by intro v hv; exact norm_le_zero_iff.mp (by have hh:= H.lower v; change _ ≤ _*g k _ at hh; simpa [hv,hf] using hh)))
       exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank D'.finrank_eq).mp hi⟩
    classical
    let L(k):Col X≃ₗ[ℂ] S.Field D:=if h:Bijective (Y k) then LinearEquiv.ofBijective _ h else D'
    let H:= max K J; have hH : K≤H:=le_max_left ..
    have hf:1≤H:=hk.trans hH
    obtain ⟨l,hl⟩:= chooses U (M:=M) P (d:=D) h i hZ hP.speed N hn -- order
    obtain ⟨hL,h₂⟩:=sitespec h hP.speed he N hn
    refine ⟨N,Z,L,H,l,(le_max_left ..).trans hδ.le, ⟨hn,hf⟩,(hy.and hZ).mono (fun k hk h=>⟨hk.2 h, by change (L k).toLinearMap= _; rw [show L k = LinearEquiv.ofBijective _ (hk.1 h) from dif_pos _]; rfl⟩), ⟨hL,h₂.mono (fun _ he=>he.2.1)⟩,?_,?_,?_⟩
    · filter_upwards [hl,ht,hZ,hδ',hy] with k h1 h2 h3 h4 h5 hx
      obtain ⟨he,hp⟩:=h2 hx
      rw [show L k=_ from (dif_pos (h5 hx):L k=_)]
      refine ⟨⟨hf,fun x=>(he.upper x).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg _)),fun x=>(he.lower x).trans (mul_le_mul_of_nonneg_right hH (Real.sqrt_nonneg _)),he.combine,he.scalar⟩,hp,h1.2 hx,fun a x=> ?_,h1.1⟩
      exact (h4 (Z k) (h3 hx) a x).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (mass_nonneg ..))
    · refine ⟨fun i v=>?_ ,?_⟩
      · exact Desk.fits Q hQ D i v -- name
      obtain ⟨-,r,l,-,-,hP'⟩:=hF₁
      filter_upwards [hP',hy,ht,hP.offers D] with k h1 h2 hh hw hx
      obtain ⟨v,hV,-⟩:=h1.2.2 (hw hx)
      simp only [lamp_torch] at h1
      refine ⟨h1.1,h1.2.1,?_,v,?_⟩
      swap
      · simpa only [lens,Arche.here,Nat.cast_one,mul_one, lamp_torch, Function.comp_apply] using! hV
      have he:= (hh hx).1
      have hi : L k= LinearEquiv.ofBijective (Y k) (h2 hx):=dif_pos (h2 hx)
      rw [hi]; exact ⟨hf,fun x=>(he.upper x).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg _)),fun x=>(he.lower x).trans (mul_le_mul_of_nonneg_right hH (Real.sqrt_nonneg _)),he.combine,he.scalar⟩
    filter_upwards [hz',(tendsto_add_atTop_nat 1).eventually hy] with k hk hi h h'
    obtain ⟨hr,Hr⟩:= (hk h).2.2 h'
    refine ⟨hr,fun x=>?_⟩
    let q':=fineprint C.path.levels (trays D) k
    have hc:1+4*K*q'≤1+4*H*q':=by nlinarith only [mul_le_mul_of_nonneg_right hH (show 0 ≤ q' from (Real.exp_pos _).le)]
    have h':L (k+1)= LinearEquiv.ofBijective _ (hi h'):=dif_pos (hi h')
    dsimp only; rw [h']; exact ⟨(Hr x).1.trans (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)), (Hr x).2.trans (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _))⟩
end YM.RG12.Alidade
