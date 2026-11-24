import YM.WilsonCoeffUV.Kinetic.Base
import YM.WilsonCoeffUV.Vacuum.UV.FirstLoop
/-!
# One-loop exact reclosure, with finite periods used only as a stencil limit

OURS Kin alpha on a compatible craft. For an Actual schedule this still
requires supplying Kin and its first 4 jet identities (including its wave
estimate). No replacement of core E1/E2. No comparison to monitor or MS.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Near Stationary PowerSeries Roam Asymptotics Tree Supply Next.Free
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{s C B:ℝ}{R:PathData G}{u: Clip}{e m N:ℕ}{A:Levels G}{Ñ:ChartRatio G}
variable {H:Horizon A}{P:Kin H Ñ}{s0: Sheet G}{R0 : Rolls s0}{B': PostCost R0}

abbrev Sponsor {Q:PathData G}(U:PathData G)(p q:Clip)(X:ChartRatio G)(α Θ γ Λ :ℝ){f c:Side}(S:StepData c f) := ∃ (ρ: fieldDir G c 1 → AxisChart G (repeatF S)), Critical (repeatF S) p Q ρ ∧ ClassicalMatch (repeatF S) p q Q U ρ ∧ FiniteBound (repeatF S) Q U p q α X ρ Θ γ Λ

lemma pivot_road {f c:Side}(S:StepData c f)(c':Side)(S':StepData c c')(h:f=c')(g:S.kernel=S'.kernel)(p:S.patch=S'.patch)(X : ChartRatio G){b t:Clip}{Q U:PathData G}{α Θ γ Λ :ℝ}(v: Sponsor (Q:=Q) U b t X α Θ γ Λ S): Sponsor (Q:=Q) U b t X α Θ γ Λ S':=by
    subst c'; rcases S with ⟨x,y,w⟩; rcases S' with ⟨a,q,e⟩; change y=q at g; change x=a at p; subst q a; exact v

lemma behemoth (h:P.Planned B')(p:m<N)(n:ℕ): let S:=mStep A (A.S.side m n) m; let j:=A.clock.J (m+1)
    Sponsor (Q:=P.path N (m+1)) (P.path N m) (A.params (m+1)).clip (A.params m).clip Ñ (P.alpha N m) (B'.Γ j) (B'.c j) (A.clock.loopCap (m+1)) S:=by
    intro S j; let V:= A.clock.op m n; apply pivot_road V _ S ?_ rfl rfl Ñ
    swap
    · apply Subtype.ext; change (A.S.side (m+1) n).val= (A.S.side m n).val * (V.patch.L).val; exact V.sizes
    exact ⟨P.stationary N m n (repeatF V),(h.critical N m n p (repeatF V)).1,h.classicalPart N m n p (repeatF V),h.retains N m n p (repeatF V)⟩

abbrev breathP (A:Levels G)(N m:ℕ){H:Horizon A}(P:Kin H Ñ) := breast (P.path N m) (A.params m).clip
abbrev hazeM (A:Levels G)(N m:ℕ){H:Horizon A}(P:Kin H Ñ)(n: Side) := front (P.path N m) (A.params m).clip n
abbrev seal_jet (A:Levels G)(N m:ℕ){H:Horizon A}(P:Kin H Ñ) := SeamPhase (A.params m).clip (P.path N m) (actionW A Ñ N m)

lemma wagerYear (hp:G.Simple)(hv:LocalRatio Ñ)(v:P.Planned B')(h:m<N) (q:seal_jet A N (m+1) P) (z:ℕ):
    let n:=A.S.side m z; let j:=A.clock.J (m+1); let W:= unripe A Ñ N m (hazeM A N (m+1) P) n; let X:=hazeM A N m P n
    (∀ i≤2,W i (2+i)= X i (2+i)) ∧ ∀ x, ‖W 2 2 x- (P.alpha N m • X 0 2 x+X 2 2 x)‖ ≤ (1/2:ℝ)*(Fintype.card (Site n):ℝ)^2*((Fintype.card (Site n):ℝ)* B'.Γ j * A.clock.loopCap (m+1)*Real.exp (-(B'.c j)*n.val)) :=by
    intro n j W X; obtain ⟨ρ,hm,h₁,h₂⟩:= behemoth v h z; let S:=mStep A n m; let F:=repeatF S
    let Q:=roam A N m n; let T:= freeForms A N m; let V:= freeForms A N (m+1)
    have ht:= tapestries S F V T Q (v.cap _ _ h) hm h₂ h₁ (horizon_step A m N h n (n*(loose A m).L) rfl) ((cond_laws A m N).1 n _ rfl) (A.blocks m 0).branches hv (age_sym A ..) (age_sym A ..) (seam_power hv hp (v.cap _ _ h) h q _)
    constructor
    · exact fun i p=> (ht.1 i p).trans (front_paths (v.cap _ _ h.le) n i).symm
    intro x; have he:=thermal_coin h₂ x; rw [draft_rate (v.cap _ _ h.le) n (P.alpha N m),Pi.add_apply, Pi.smul_apply,← ht.2] at he; exact he

lemma epochs (hp:G.Simple)(hv:LocalRatio Ñ)(v:P.Planned B')(h:m<N)(q:seal_jet A N (m+1) P) :
    let Z:=freshet A Ñ N m; let K:=breathP A N m P
    (∀ i≤2, Z i (2+i)=K i (2+i)) ∧ Z 2 2 = P.alpha N m • K 0 2 + K 2 2:=by
    intro Z K
    let C:= v.cap N (m+1) h; let V:=v.cap N m h.le; let n:=A.S.side m; let H:=period_crumb A m; let U i:= hazeM A N m P (n i); let W (i:ℕ):= unripe A Ñ N m (hazeM A N (m+1) P) (n i)
    let r x :=foldUnder (n x) (α:=Hooks G)
    have hW i j (p:i≤ 2) x: Tendsto (fun k=> W k i (j+1) (r k ∘ x)) atTop (𝓝 (Z i (j+1) x)):= ((stanza C hv h q i (j+1) (by omega)).point x).comp H
    have hZ i j x: Tendsto (fun k=> U k i (j+1) (r k ∘ x)) atTop (𝓝 (K i (j+1) x)):= ((breast_turn V i (j+1)).point x).comp H
    have hE (i j)(p:j≤2): W i j (2+j)=U i j (2+j):=(wagerYear hp hv v h q i).1 j p
    constructor
    · intro i p; rw [Nat.add_comm]; funext x; apply tendsto_nhds_unique (hW i (i+1) p x)
      apply (hZ i (i+1) x).congr; intro z; exact congr_fun (show U z i (i+1+1)=W z i (i+1+1) by rw [show i+1+1=2+i by omega, hE z i p]) _
    funext x; let Y z:= P.alpha N m • U z 0 2 (r z ∘ x)+U z 2 2 (r z ∘ x); let q':=(P.alpha N m • K 0 2+K 2 2) x; have hv0:Tendsto Y atTop (𝓝 q'):= ((hZ 0 1 x).const_smul _).add (hZ 2 1 x)
    let B k:= W k 2 2 (r k ∘ x); let J:= A.clock.J (m+1); have hu : Tendsto (B-Y) atTop (𝓝 0):=tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun z=> norm_nonneg _) (fun i=> (wagerYear hp hv v h q i).2 _) (spectral_gain (B'.Γ J) _ _ (B'.posC _) n H))
    exact sub_eq_zero.mp (tendsto_nhds_unique (show Tendsto (B-Y) atTop (𝓝 (Z 2 2 x-q')) from (hW 2 1 le_rfl x).sub hv0) hu)

lemma epic_pulse (hp:G.Simple)(hv:LocalRatio Ñ)(v:P.Planned B')(h:m<N) (q:seal_jet A N (m+1) P) : coeff 2 (pitch A Ñ N m)= P.alpha N m:=by
    let B:=breathP A N m P; have he:=epochs hp hv v h q
    let Y:= freeForms A N m
    have hZ : B 0 2= orbQ (plain G Y):=(he.1 0 (by omega)).symm.trans (show freshet A Ñ N m 0 2=_ from by rw [show freshet A Ñ N m 0=_ from (perch A Ñ hp hv h).lead,shine_lit])
    have hp' :=v.cap N m h.le
    obtain ⟨s,T,hS,hT⟩:= (breast_turn hp' 0 2).cover; obtain ⟨s',V,hV,hU⟩:=(breast_turn hp' 2 2).cover
    rw [pitch,stellar_read, he.2, sun_add (hT.smul (P.alpha N m)) hU hS hV, sun_μ];
    change _ * readSun (B 0 2) +readSun (B 2 2)= _
    rw [pricedR hp' hp,hZ, crown_read hp]; simp

lemma old_levels (hp:G.Simple)(hv:LocalRatio Ñ)(h:m<N)(k:ℕ):
     actionW A Ñ N m k (2+k)= freshet A Ñ N m k (2+k):=by
     let R:= ratioHigh A Ñ N m; let P:=lop (freshet A Ñ N m)
     have he : constantCoeff R=1:=back_cc (angle_tilt hp hv h); have hu : shellK 2 P:= shell_lop (post_near hp hv h)
     rw [conduct A Ñ h]; change Blue.mix R P k _=_
     unfold Blue.mix; rw [Finset.sum_eq_single k];
     · simp only [Nat.sub_self,coeff_zero_eq_constantCoeff_apply,map_mul,map_pow,constantCoeff_inv,he,one_pow,inv_one,mul_one,one_smul]; exact dif_neg (by omega)
     · intro i hi hb; rw [hu i (2+k) (by have ht:=Finset.mem_range.mp hi; omega),smul_zero]
     simp
lemma chant (hp:G.Simple)(hv:LocalRatio Ñ)(v:P.Planned B')(h:m<N) (q:seal_jet A N (m+1) P) :
    actionW A Ñ N m 2 2= breathP A N m P 2 2:=by
    let E:= breathP A N m P; let B:= E 2 2; let a:= P.alpha N m; let U:=orbQ (plain G (freeForms A N m));
    have hs:=epochs hp hv v h q; have hx:= hs.2
    have hz:freshet A Ñ N m 0 2 = U:=by rw [show freshet A Ñ N m 0=_ from (perch A Ñ hp hv h).lead,shine_lit]
    have hp': E 0 2=U := (hs.1 0 (by omega)).symm.trans hz
    let F:=lop (freshet A Ñ N m); have h₁:F 0 2=U:=hz
    have h₂:F 2 2=a • U+B:=by rw [←hp']; exact hx
    let R:=ratioHigh A Ñ N m; have hR:constantCoeff R=1:=back_cc (angle_tilt hp hv h)
    have he:= (perch A Ñ hp hv h).parityC; have hb:evenC R:= even_back (angle_tilt hp hv h) he
    have hk:constantCoeff R⁻¹=1:=by simp [hR]
    have hf:coeff 2 ((R⁻¹)^2)= -a:=by
       have hy : R^2 * R⁻¹^2=1:=by rw [← mul_pow,PowerSeries.mul_inv_cancel R (by exact hR ▸ one_ne_zero),one_pow]
       have hx:= congr_arg (coeff (R:=ℝ) 2) hy
       let Z: ℝ:=a
       have hr: coeff 2 R= (1/2:ℝ)*a:= by unfold R; rw [Bloom.back_fee hp hv h,epic_pulse hp hv v h q]
       have hL:coeff 2 (R^2)=a:=by rw [pow_two,coeff_mul,show Finset.antidiagonal (2:ℕ)={(0,2),(2,0),(1,1)} by decide]; simp [hr,hR,hb 1 (by decide)]; ring
       rw [coeff_mul,show Finset.antidiagonal (2:ℕ)={(0,2),(2,0),(1,1)} by decide] at hx; norm_num [hb 1 (by decide),even_pow hb 2 1 (by decide), even_pow (even_inv hb hR) 2 1 (by decide), hL,hk,hR] at hx; linarith
    rw [conduct A Ñ h]; change Blue.mix R F _ _=B; unfold Blue.mix
    simp only [Finset.sum_range_succ, Finset.range_zero,Finset.sum_empty,h₁,h₂]; norm_num [hf,hR,hk, even_mul hb (even_pow (even_inv hb hR) 2) 1 (by decide)]
lemma bellows (hp:G.Simple)(hv:LocalRatio Ñ)(v:P.Planned B')(h:m<N) (q:seal_jet A N (m+1) P) : seal_jet A N m P:=by
    let U:=actionW A Ñ N m; have hx:= catchment A Ñ hp hv h.le; let Z:=breathP A N m P
    constructor; intro i hi
    ext1 j; change Z i j=U i j
    have he:=v.cap N m h.le
    by_cases p:j≤1
    · apply (breast_nil he i j (Or.inl p)).trans; interval_cases j
      · exact (congr_fun (congr_fun hx.empty i) 0)
      exact (hx.vanishes i).symm
    by_cases ht:j=2+i; subst j; exact (epochs hp hv v h q).1 i (by omega) |>.symm.trans (old_levels (A:=A) (Ñ:=Ñ) hp hv h i).symm
    by_cases H:j=i
    · have h':j=2:=by omega
      subst i; subst j; exact (chant hp hv v h q).symm
    refine (front_span he i j ht H).trans ?_; by_cases hz:j>2+i; exact (hx.rank i j (by omega)).symm
    exact (hx.grade i j (by omega)).symm

theorem alpha_stable (hp:G.Simple)(hv:LocalRatio Ñ)(v:P.Planned B')(h:m≤N) : SeamPhase (A.params m).clip (P.path N m) (actionW A Ñ N m) ∧ (m<N → coeff 2 (pitch A Ñ N m) = P.alpha N m):=by
    induction h using Nat.decreasingInduction with
    | self=> exact ⟨breast_top v N,fun p=> (lt_irrefl N p).elim⟩
    | of_succ i h ih=> exact ⟨bellows hp hv v h ih.1,fun _=> epic_pulse hp hv v h ih.1⟩
end YM.WilsonCoeffUV.Bank.Mosaic
