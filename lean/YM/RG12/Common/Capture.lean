import YM.RG12.Common.Short
/-!
# Result: all induced k prices (`ReadingAt`) at one common moving measurement

No gaps in k. Uses same Construction and admissible Phase/Final through consumers, fixed
rational reflection shape, a_k up to at most polynomial log for lengths. Not comparing
frames/measurements from k to k+1!
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Commission
open Function Filter Lattice Wilson RG RG.Supply Next.Rank Next.Rank.Tapes Next.Rank.Perch Next.Rank.Station Real Asymptotics Ship Peak
open PhysicalNext PhysicalNext.RankCovariance PhysicalNext.InteractingRank.Soft
open MergeProof MergeProof.East Next.Rank.Tapes.West MergeProof.Accent
open Pert.Dense Spec Bid YM.RG12.Arche
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}
variable {M:∀ d,ℕ→RepChart C d} {ϕ:Filter UVIndex} [ϕ.NeBot]
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "κ" k:max=> C.S.a k
variable {S : Table C.book} {f: Extraction.Order}(F:Final C f S) (ax:Axis)
variable (h:Observing C F.room.cutoff ϕ M) (he : ϕ  ≤  f.fuse)
variable (P:Port C)(hp:Covered P F.room.cutoff) (H:G.Simple)

lemma Lamps.inv {t k d:ℕ} {r:ℝ}{V:Module.End ℂ (C.label d)} (T:Lamps (C:=C) t k d r M V): Bijective V:=by
  have hv: Injective V:= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (by
    intro v hh; have hx:= T.lower v; rw [hh,show mass C d 0=0 from by simp [mass,Labels.Frame.coeffSize],mul_zero] at hx; exact Work.G08.size_separates _ _ hx))
  exact ⟨hv,LinearMap.surjective_of_injective hv⟩
local notation "chol"=> (A).clock.hatBeta
lemma later_rate (hG:G.Simple)(u v:ℕ)(hv:u ≤ v): chol u  ≤  chol v:=by unfold Calendar.hatBeta; gcongr; exact (Gauge.slopeConstant_pos hG).le; exact scale_mono (A) hv
variable {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{L:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (hs:Scrim C W u ψ φ δ (PhysicalNext.Repeat.Legato.Bandage.fly C.path.levels) r L)
include P hp H h he hs
lemma diagram (Q:OPE.Prescription F.sector.derivatives)(hq:Q.Coherent)(D Nmin:ℕ):
    let Z:= Desk.Sector F.sector.derivatives D; let V:= Frames.Col Z; let X:=fun k=>engineering (S:=S) M D k
    ∃ (N:ℕ),Nmin<N ∧ let scope:= Arche.Shapes.scope ax N; ∃ t:ℕ→ℝ, Tendsto t atTop (𝓝 0) ∧
    ∃ c K : ℝ, 0<c ∧ 1  ≤  K ∧ ∀ᶠ k in atTop, let p := Desk.Paired.sampleForm F scope D (t k)
    C.S.a k  ≤  t k ∧ t k  ≤  C.S.a k * (chol k)^3 ∧ ∃ Y:V→ₗ[ℂ] C.label D,
    Nonempty (ReadingAt C S D Z (fun x=> Real.sqrt (p.eval x)) k M Y (D+3)) ∧
    (∀ v,c*‖v‖^2  ≤  p.eval (X k (Y v)))∧ (∀ v,p.eval (X k v)  ≤  K * (chol k)^2 * mass C D v^2):=by
  intro Z V X
  let T := P.panels D; let p:= P.rate; let i:Fin 3:=0
  obtain ⟨N,hn,HT⟩:= Arche.principal T P.chart F.room.cutoff H hs P.haar P.locality _ (hp.2.1 D) i F ax h he 1 (by decide) (n:=trays D) (by unfold trays; omega) Q hq Nmin
  obtain ⟨ht,c,K,hc,hK,hT⟩:= HT
  let t k := lamp C N k (mag A (T i).arc k)
  let Λ k:= t (P.rate k)
  refine ⟨N,hn,Λ,ht.comp hp.1,c,K,hc,hK,?_⟩
  filter_upwards [hp.1.eventually hT,hp.2.2 D,hp.1.eventually_ge_atTop (C.ref D)] with k hk hD hE γ
  let j:= P.rate k; let r:=κ j / κ k; let q:= chol k; let q':=chol j
  have h1 : 1  ≤  q:= (A).fits.delayed _ |>.le
  have hv : 0  ≤  κ k:= (C.S.a_pos _).le; have hs := pow_le_pow_left₀ (show 0  ≤  q' from zero_le_one.trans (A|>.fits.delayed j).le) (later_rate H j k hD.1) 2
  refine ⟨(C.S.strictAnti.antitone hD.1).trans hk.1,?_,?_⟩
  · change t j  ≤  _
    apply hk.2.1.trans
    have hf := hD.2.1
    exact (mul_le_mul (show κ j  ≤  q * κ k from (div_le_iff₀ (C.S.a_pos _)).mp hf) hs (sq_nonneg _) (mul_nonneg (zero_le_one.trans h1) hv)).trans_eq (by unfold q; ring)
  obtain ⟨Y,⟨hY⟩,hM,hN⟩:= hk.2.2 hD.2.2
  have hγ(v): (here F ax D N (↑(1:ℕ)) (t j)).eval v=γ.eval v:=by change (Desk.Paired.sampleForm F _ _ _).eval v = _; simp [γ,Λ,j] -- t j reduces
  obtain ⟨A0,hP⟩:= passage F.room.cutoff h (t:=j) hE hD.1
  let V' := LinearEquiv.ofBijective A0 hP.inv
  have hp':0<r:=div_pos (C.S.a_pos _) (C.S.a_pos _)
  have ht : r ≤ q:= hD.2.1
  have hκ':0  ≤  q:=zero_le_one.trans h1
  have hw(v): X j (V' v)= X k v:=by
     unfold X; rw [engineering_at,engineering_at]
     simp_rw [Complex.ofReal_pow]; have he:= congr_arg (fun x:C.label D=>S.project D x) (hP.pulls v); simp only [map_smul] at he; exact he
  let W': V→ₗ[ℂ] C.label D:= V'.symm.toLinearMap.comp Y
  refine ⟨W',⟨⟨?_,?_,?_⟩⟩,fun v => ?_,fun v=> ?_⟩
  · intro v; rw [← hw v, ← hγ]
    apply (hY.look (V' v)).trans
    have hx:mass C D (V' v)  ≤  q*mass C D v:= (hP.norms v).trans (mul_le_mul_of_nonneg_right ht (mass_nonneg ..))
    refine (mul_le_mul hs hx (mass_nonneg ..) (sq_nonneg _)).trans ?_
    rw [← mul_assoc,← pow_succ]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1 (by omega)) (mass_nonneg ..)
  · intro x;let v:= W' x; have hb: A0 v=Y x := V'.apply_symm_apply _
    have hv:= hP.lower v; rw [hb] at hv
    apply hv.trans
    calc
      _  ≤  q^(D+1) * (q'^2*‖x‖):= mul_le_mul (pow_le_pow_left₀ hp'.le ht (D+1)) (hY.norm x) (mass_nonneg ..) (pow_nonneg hκ' _)
      _  ≤  q^(D+1) * (q^2*‖x‖):=by gcongr
      _ = _ :=by unfold q; ring
  · intro x
    let v:= W' x; have hb : V' v= Y x:=V'.apply_symm_apply _
    have ht' := (pow_le_pow_right₀ h1 (show 2 ≤ D+3 by omega))
    change _ ≤  _*Real.sqrt (γ.eval (X k v)); rw [← hw v,hb,← hγ]; exact (hY.price x).trans (mul_le_mul_of_nonneg_right (hs.trans ht') (Real.sqrt_nonneg _))
  · rw [← hw (W' v),← hγ]; change _  ≤  (here F ax D N (↑(1:ℕ)) (t j)).eval (X j (V' (V'.symm (Y v)))) ; rw [LinearEquiv.apply_symm_apply]; exact hM v
  rw [← hw v,← hγ]; apply (hN _).trans; rw [mul_assoc,← mul_pow]
  have hx:=mass_nonneg C D (V' v); gcongr; exact (hP.norms v).trans (mul_le_mul_of_nonneg_right ht (mass_nonneg ..))
end YM.RG12.Commission
