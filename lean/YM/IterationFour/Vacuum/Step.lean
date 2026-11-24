import YM.IterationFour.Vacuum.Reclose
import YM.IterationFour.Denominator
import YM.IterationFour.Vacuum.Render
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Opening

/-!
# Use at the pinned vacuum representation

Same history and same local step output. `Early` is local Hloc estimate priced at
specific alignment on that polynomial; pay the remaining α and uncertain-delta
costs HERE. No estimate on the norm of an arbitrary density is being assumed.
The induction interface downstream can also use the top (Wilson initial) case
of `resume`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Vacuum
open Lattice Wilson RG Function MeasureTheory Filter
open Currency Render Progress.DirectedRecipe AnalyticBridge VerifiedReset Averaging Collection
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

/-- Fields held fixed even if an exact re-expression changed the address mechanism, etc. -/
structure Storage (C : Family G) (N q m : ℕ) (U : RG.Rep G (C.side m q)) : Prop where
    stencil : U.path = (C.path.rep N q m).path
    clip : U.clip=(C.path.levels.params m).clip
    budget : U.p=C.path.levels.budget m

/-- The complete unmarked result, including residue. -/
def loaded (C : Family G) (N q i : ℕ) (S : List (Piece G (C.side i q)))
    (U : RG.Rep G (C.side i q)) := Render.append S U (prefactor (g C N q i))

/-- A rerendering with a proved small gap (denominated as beta, not g). Do not
    push with the coupling changed to U.beta. -/
structure Coin (C : Family G) (N q i : ℕ) (S : List (Piece G (C.side i q)))
    (U : RG.Rep G (C.side i q)) (x γ l : ℝ) : Prop where
    types : Storage C N q i U
    error : U.activities.Valid (C.path.levels.budget i) x γ
    total : (loaded C N q i S U).activities.Valid (C.path.levels.budget i)
      (C.path.levels.clock.allowance i) (C.path.levels.clock.forcedAllowance i)
    lives : permits S (C.path.levels.budget i)
    value : (loaded C N q i S U).eval=(C.path.rep N q i).eval
    extraBeta : |U.beta-C.path.β N q i| ≤ l

namespace Coin
variable {C : Family G} {N q i : ℕ} {S} {U : RG.Rep G (C.side i q)} {x γ l : ℝ}
    (h : Coin C N q i S U x γ l)
include h
lemma enlarge {y : ℝ} (he : x≤y) : Coin C N q i S U y γ l :=
    { h with error:={h.error with boundE:= Time.E_rises h.error.boundE he} }
lemma loosen {y μ : ℝ} (he : γ≤y) (hμ : l≤μ) : Coin C N q i S U x y μ :=
    { h with error:={h.error with boundK:= Time.K_rises h.error.boundK he}
             extraBeta:=h.extraBeta.trans hμ }
include h
lemma lawful (ht : C.Makes) (hi : i≤N) :
    (loaded C N q i S U).Lawful (C.path.levels.params i).width (C.path.levels.params i).paths
      (C.path.levels.clock.loopCap i) (C.path.levels.clock.allowance i) (C.path.levels.clock.forcedAllowance i) := by
  have hs := ht.wilson.represents N q i hi
  constructor
  · change U.path.Bounds U.clip ..
    rw [h.types.stencil,h.types.clip, ← hs.clip]; exact hs.good.paths
  change Activities.Valid _ U.p _ _
  rw [h.types.budget]; exact h.total

lemma scalar (ht : C.Makes) (hi : i≤N) : U.v=(C.path.rep N q i).v := by
  have hs := U.scalar
  have hx:= Real.exp_injective (
    ((SectorNext.Vacuum.flat_density _ (h.lawful ht hi)).symm.trans (congr_fun h.value 1)).trans
    (SectorNext.Vacuum.flat_density _ (ht.wilson.represents N q i hi).good))
  exact mul_right_cancel₀ ((SectorNext.Vacuum.site_pos _).ne') hx

/-- The spatially flat correction is explicitly identifiable. Real at
    H.beta, kernel uses it without shifting, *THIS* is the extra non-affine
    term (value everywhere, not just on healthy masks). Do NOT include in the
    affine-null bound. -/
lemma read_exponent (ht : C.Makes) (hi : i≤N) (V) :
    (loaded C N q i S U).exponent V = (C.path.rep N q i).scalar -
      ((C.path.rep N q i).path.inChannels U.clip U.p (C.path.β N q i) V +
        (U.beta-C.path.β N q i)*YM.Push.BetaTransport.kinetic U.path U.clip U.p V) -
      ((loaded C N q i S U).activities).additive U.p V := by
  rw [← h.types.stencil]
  change U.scalar - U.path.inChannels U.clip U.p U.beta V - (loaded C N q i S U).activities.additive U.p V = _
  rw [YM.Push.BetaTransport.channels_split V U.beta,
    YM.Push.BetaTransport.channels_split V (C.path.β N q i),
    show U.scalar = (C.path.rep N q i).scalar from congr_arg (· * _) (h.scalar ht hi)]
  ring
lemma paid_partition (ht : C.Makes) (hi : i≤N) : (∫ V, (loaded C N q i S U).eval V ∂prior G _) =
    partition G (C.side N q) (C.beta N q) := by rw [h.value]; exact History.partition_eq _ ht.wilson _ _ _ hi
lemma positive (ht : C.Makes) (hi : i≤N) (V) : 0 < (loaded C N q i S U).eval V := by
  rw [h.value]; exact SectorNext.Vacuum.strictly _ ht.wilson _ _ _ hi _
omit h
lemma denominator_along {L M : ℕ} {V} {W w} {T}
    {y t f : ℝ} (h : Coin C N L (M+1) W V y t f)
    (hv : Coin C N L M T w x γ l) (ht : C.Makes) (hi : M<N) :
    Denominator.denominator C N L M (loaded C N L _ W V)=(loaded C N L M T w).eval :=
      (Denominator.denominator_real C ht hi _ h.value).trans hv.value.symm
end Coin

/-- Local prereset estimate *before* α reclosure. `b` is the coarse predicted inverse
    coupling from independent Fk/A readout on the incoming masks (on unmasked germs
    there, then transported, incl local-error correspondence), while α chosen as how
    much of b is not yet clipped. Both initial and subsequent steps use this interface.
    Producer of `exactly` must retain mask identities, older gas, normalization, etc.
    x already contains any bill for moving rendered/model paths at this comparison. -/
structure Early (C : Family G) (N q i : ℕ) (S : List (Piece G (C.side i q)))
    (X : Listing G (C.side i q)) (v : Collection.Source G (C.side i q)) (τ : ℝ)
    (β α H w : ℝ) (F : Config G (C.side i q) → ℝ) : Prop where
    bud : Local X (C.path.levels.budget i) v H w
    exactly : F = fun V=>
      Reset.supplied (C.path.rep N q i).path (C.path.levels.params i).clip
        (C.path.levels.budget i) X v (β-α) τ α V * Real.exp
          (-renders (prefactor (gain β)) (C.path.levels.budget i) V S)

/-- Early inputs go to this concrete unmarked output (append printed model S
    at *actual* coupling to see the result). -/
def reclosed (C : Family G) (N q i : ℕ) (S : List (Piece G (C.side i q)))
    (X : Listing G (C.side i q)) (v : Collection.Source G (C.side i q)) (τ β α : ℝ) : RG.Rep G (C.side i q) :=
  Render.append S
    (Reset.after (C.path.rep N q i).path (C.path.levels.params i).clip (C.path.levels.budget i)
      X v (β-α) τ α) (prefactor (gain β)-prefactor (g C N q i))

/-- Rigidity receipt (applies uniformly even changing volume). -/
def FixedWave (C : Family G) (m : ℕ) (l : ℝ) : Prop := ∀ N q, m≤N → ∀ U : RG.Rep G (C.side m q),
    U.Lawful (C.path.levels.params m).width (C.path.levels.params m).paths (C.path.levels.clock.loopCap m)
      (C.path.levels.clock.allowance m) (C.path.levels.clock.forcedAllowance m) →
    U.p=C.path.levels.budget m → U.eval=(C.path.rep N q m).eval → |U.beta-C.path.β N q m| ≤ l
lemma waves {C : Family G} (hg : G.Simple) (h : C.Makes) (Q : ℝ) :
    ∀ᶠ m:ℕ in atTop,FixedWave C m (weight C.path.levels Q m) := by
  obtain ⟨q,hQ⟩ := exists_nat_ge Q
  filter_upwards [IterationFour.Kinetic.rigidity C hg h q,IterationFour.Kinetic.quote_eventually C hg] with m hm ht
  intro N p he U hr hu hx
  apply le_trans (hm N p he U hx _ _ _ _ _ hr (hu.symm ▸ ht))
  exact beta_gap_power _ _ _ (by linarith only [hQ,Nat.cast_nonneg (α:=ℝ) q])

/-- Kinetic uncertainty in beta units from measuring the early error. -/
def conversion (a : Levels G) (i : ℕ) (l H : ℝ) := H/((a.budget i).threshold^2)+l
/-- Pre-L part of reset. -/
def adjusting (a : Levels G) (i : ℕ) := Time.base G (a.params i)
/-- Which output regular budget after closure. -/
def owed (a : Levels G) (i : ℕ) {n : Side} (S : List (Piece G n)) (l H : ℝ) :=
    adjusting a i * H + shiftBill S (B a i)*conversion a i l H

def Duty (a : Levels G) (i : ℕ) (α H w γ : ℝ) :=
    Reset.charge G (a.budget i) (a.params i).clip (a.params i).width (a.params i).paths α H w γ

/-- Install any funded affine-reset intermediate T at its OWN output beta.
    Scalable bills before viability tests on marked stamp. This extraction
    factored out for uses with additional exact bookkeeping already ON T. -/
lemma useful (C : Family G) (ht : C.Makes) {N q i : ℕ} (hi : i≤N)
    {S β H γ} (T:RG.Rep G (C.side i q))
    (hT' : Storage C N q i T)
    (hT : T.activities.Valid (C.path.levels.budget i) (adjusting C.path.levels i*H) γ)
    (hm : permits S (C.path.levels.budget i)) (hf : β∈stripe (B C.path.levels i))
    (hp : (C.path.levels.budget i).threshold^2 * |T.beta-β|≤ H)
    (hv : (Render.append S T (prefactor (gain β))).eval=(C.path.rep N q i).eval)
    {l : ℝ} (hl : 0≤l) (hw : FixedWave C i l) (hγ : γ ≤ C.path.levels.clock.forcedAllowance i)
    (hc : owed C.path.levels i S l H + unitBill S (B C.path.levels i) ≤ C.path.levels.clock.allowance i) :
    let U:=Render.append S T (prefactor (gain β)-prefactor (g C N q i))
    Coin C N q i S U (owed C.path.levels i S l H) γ l ∧ |β-C.path.β N q i| ≤ conversion C.path.levels i l H := by
  intro R
  cases T with | mk u v w x y z=>
    obtain ⟨ha,hb,he⟩:=hT'
    change u=_ at ha; change v=_ at hb; change x=_ at he; subst u; subst v; subst x
    let a:=C.path.levels; let b:=C.path.β N q i; let u:=B a i; let W:=C.path.rep N q i
    let P := a.params i; let p := a.budget i; let D:=adjusting a i*H
    let T := (⟨W.path,P.clip,w,p,y,z⟩ : RG.Rep G _)
    let M:= Render.append S T (prefactor (gain β))
    have hpaths : W.path.Bounds P.clip P.width P.paths (a.clock.loopCap i) := by
       have he := ht.wilson.represents N q i hi; rw [← he.clip]; exact he.good.paths
    have hz : 0 ≤ conversion a i l H := add_nonneg (div_nonneg ((mul_nonneg (sq_nonneg _) (abs_nonneg _)).trans hp) (sq_nonneg _)) hl
    have hN:= shift_nn S hm (WardBin.hot a i)
    have hJ : M.activities.Valid p (a.clock.allowance i) (a.clock.forcedAllowance i) := by
      have he := addition (R:=T) (Render.prefactor (gain β)) hm hT
      have hy : D ≤ owed a i S l H := le_add_of_nonneg_right (mul_nonneg hN hz)
      have hh := (add_le_add hy (unit_span S hm (WardBin.hot a i) hf)).trans hc
      exact { he with boundE:= Time.E_rises he.boundE hh, boundK:= Time.K_rises he.boundK hγ }
    have hF : |T.beta-b| ≤ l:= hw N q hi M ⟨hpaths,hJ⟩ rfl hv
    have hJ : |β-b| ≤ conversion a i l H := by
       have h: |T.beta-β| ≤ H/p.threshold^2 := (le_div_iff₀ (sq_pos_of_pos p.threshold_pos)).2 ((mul_comm ..).trans_le hp)
       change _ ≤ H/p.threshold^2+l; rw [show β-b=T.beta-b-(T.beta-β) by abel,← Real.norm_eq_abs]; exact (norm_sub_le ..).trans ((add_le_add hF h).trans_eq (add_comm ..))
    refine ⟨?_,hJ⟩
    let O:= owed a i S l H
    let j':Piece G (C.side i q) → ℝ:=Render.prefactor (gain b)
    let x':Piece G (C.side i q) → ℝ:=prefactor (gain β)
    have hiR : R.activities.Valid p O γ := by
      have he' := Render.addition (R:=T) (x'-j') hm hT
      have hy : dollars (fun i=> ‖(x'-j') i‖) S ≤ shiftBill S u *conversion a i l H :=
        (change_b S hm (WardBin.hot a i) hf (actual_band ht N q i hi)).trans (mul_le_mul_of_nonneg_left hJ hN)
      exact { he' with boundE:= Time.E_rises he'.boundE (add_le_add_right hy _) }
    have hd := Render.addition (R:=R) j' hm hiR
    exact ⟨⟨rfl,rfl,rfl⟩,hiR,
      { hd with boundE := Time.E_rises hd.boundE ((add_le_add_right (unit_span S hm (WardBin.hot a i) (actual_band ht N q i hi)) _).trans hc)
                boundK := Time.K_rises hd.boundK hγ }, hm, (actual_reset S (R:=T) hm hT x' j').trans hv,hF⟩

lemma resume (hg : G.Simple) (C : Family G) (ht : C.Makes) {N q i : ℕ} (hi : i≤N)
    {S X v τ β α H w} {F : Config G (C.side i q) → ℝ} (hx : Early C N q i S X v τ β α H w F)
    (he : F=(C.path.rep N q i).eval) (hm : permits S (C.path.levels.budget i)) (hf : β∈stripe (B C.path.levels i))
    {γ : ℝ} (hd : Duty C.path.levels i α H w γ)
    (hγ : γ ≤ C.path.levels.clock.forcedAllowance i)
    {l : ℝ} (hl : 0≤l) (hw : FixedWave C i l)
    (hc : owed C.path.levels i S l H + unitBill S (B C.path.levels i) ≤ C.path.levels.clock.allowance i)
    (hn : WilsonStartup.Decent (C.path.levels.params i).clip (C.path.levels.budget i))
    (hσ : Geo.Width (C.path.levels.budget i) (C.path.levels.params i).clip (C.path.levels.params i).width) :
    let R:= reclosed C N q i S X v τ β α
    Coin C N q i S R (owed C.path.levels i S l H) γ l ∧
      |β-C.path.β N q i| ≤ conversion C.path.levels i l H ∧
      R.beta=β+delta (X.read v) ∧ R.v=vac v τ := by
  intro R
  let a:=C.path.levels
  let P := a.params i; let p := a.budget i
  let Δ:= delta (X.read v); let u:=B a i; let b:=C.path.β N q i
  let W:= C.path.rep N q i
  let T:= Reset.after W.path P.clip p X v (β-α) τ α
  let D:= adjusting a i*H
  let M:= Render.append S T (prefactor (gain β))
  have hsize : 20 < (C.side i q).val := by have h:= a.fits.sizeT i q; change _ ≤ (C.side i q).val at h; omega
  have hpaths : W.path.Bounds P.clip P.width P.paths (a.clock.loopCap i) := by
    have he := ht.wilson.represents N q i hi; rw [← he.clip]; exact he.good.paths
  have hdP := Reset.allocated hg hsize hpaths hx.bud hn hσ α hd
  have hk : T.beta=β+Δ := by change β-α+α+_=β+Δ; rw [sub_add_cancel]
  have hT : T.activities.Valid p D γ := by
    have hz : regularNeed G p P.clip P.width P.paths 0 H = D := by
      simp [Time.table G P (show Time.Same P p from ⟨rfl,rfl,rfl⟩), D,P,adjusting]
    rw [← hz]; exact hdP.gates ..
  have hM : M.eval=W.eval := by
    rw [← he,hx.exactly]
    funext U
    rw [show M.eval U= _ from Render.generated (R:=T) (prefactor (gain β)) hm hT U, show T.eval = _ from Reset.debited hg hsize hpaths hx.bud hn hσ α (β-α) τ hd]
    rfl
  have hh: T.beta-β=Δ:=by rw [hk]; ring
  obtain ⟨hy,hQ⟩:= useful C ht hi T ⟨rfl,rfl,rfl⟩ hT hm hf (hh.symm ▸ (delta_bound hg hx.bud.projects)) hM hl hw hγ hc
  exact ⟨hy,hQ,hk,rfl⟩
end YM.IterationFour.Vacuum
