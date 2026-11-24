import YM.Pier.Scene.Crown
/-! Extend to full regular singleton field points. Truncation error paid even
    when the moments are read in the actual `scene` law. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe.Panoramic
open Pier.Scene Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G} {k z i j l m p N d:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ) (T₀ : Citizen C W r D)
set_option quotPrecheck false

abbrev regularRead (C:Family G)(d k N p:ℕ)(v:C.label d)(x: Site (C.side k p)) :=
  indexX C d N p v (loops C k p x) (1,false) k
open Vitrines
include H T₀
local notation "x*"=> (0: Site (C.side k p))
local notation "K"=> (C.path.rep N p k)
local notation "B" => (C.path.levels.budget k).B
local notation "c"=> (C.path.levels.params k).columns
lemma enamelCost (z:Site (C.side k p)) (hk:C.ref d ≤ k) (hl:C.ref 0<k) (ht:k<N) (u:C.label d) {v:ℝ}
    (hb : Spindle.paid C d k N p u ≤ v) :
    Envelope (regularRead C d k N p u z) ∧ Envelope (bead C d k N p B u z) ∧
    ∀ U,‖regularRead C d k N p u z U‖ ≤ 3*(c*v) ∧
     ‖regularRead C d k N p u z U - bead C d k N p B u z U‖ ≤ 2*(Real.exp (-2*(B:ℝ))*(c*v)) ∧
      ‖bead C d k N p B u z U‖ ≤ 5*(c*v) := by
  let Q:= parcel C d k N p u
  let s:= (c)
  let A:= alto C.path k d
  let g:= Real.exp (-2*(B:ℝ)); have ha:1≤ s:= (C.path.levels.params k|>.columns_ge)
  have hw:= mul_le_mul_of_nonneg_left hb (zero_le_one.trans ha)
  have h(j): ‖regularRead C d k N p u z j‖ ≤ 3*(s*v) := (scratch C u k p N (1,false)
    (loops C k p z) H.seed hk ht.le j).1.trans (mul_le_mul_of_nonneg_left hw (by norm_num))
  let F:= C.labels.level d; let x:= s*F.coeffSize (F.core Q.x)
  let X₀:=Q.exponentialEntry 0 (C.localSection d) K
  let V:=pull 1 z («K»:=G.El)
  have hZ: Q.Format 0 C.params K:= (H.seed.calibrated d N p (hk.trans ht.le)).format k hk ht.le _
  have hr: Real.exp (-(2:ℝ)*(B:ℝ)) ≤ 1:= Real.exp_le_one_iff.mpr (by simp)
  have hT:Measurable X₀:=(measurable_const.add (masked_measurable _ _ _ ((C.localSection d).continuous_places ..).measurable)).add (Measurable.tsum (fun i=> masked_measurable _ _ _ (hZ.smooth i).borel))
  have hx(u':Config G (C.side k p)): regularRead C d k N p u z u' = A*X₀ (V u'):= by unfold regularRead indexX; rw [Ribbons.same C k p z]; rfl
  refine ⟨⟨(funext hx).symm ▸ measurable_const.mul (hT.comp (continuous_pull ..).measurable),_,h⟩,
    GridApprox.cylinder_env (bead_local H z u hk ht.le _),fun U=>?_⟩
  have hτ : ‖A‖*x ≤ s*v:= (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (rotate_core F _) (zero_le_one.trans ha)) (norm_nonneg A)).trans ((mul_left_comm ‖A‖ s _).trans_le (mul_le_mul_of_nonneg_left ((mintedLabel (p:=p) (k:=k) (N:=N) u).symm.trans_le hb) (zero_le_one.trans ha)))
  obtain ⟨ι,I',M,w,H'⟩:= Vitrines.drifts (C:=x) (H.strong (p:=p) hl ht.le) hZ (T₀.torches d N p k hk ht _) (B)
  have hv : ‖drift (K) Q (B) (V U)‖ ≤ 2*(g*x) := by
     rw [H'.lit]; simp only [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,zero_add]
     exact (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i _=> (norm_smul ..).trans_le (mul_le_mul_of_nonneg_left
       ((frame_fee (M i) (V U)).trans (K|>.p.loMass _ _ (M i).profit)) (norm_nonneg (w i))))).trans H'.pay)
  have hS: ‖regularRead C d k N p u z U - bead C d k N p B u z U‖ ≤ 2*(g*(s*v)):=by
    rw [hx]; change ‖A*X₀ (V U)-A*(X₀ (V U)-_)‖ ≤ _; rw [← mul_sub A,sub_sub_cancel,norm_mul]
    exact (mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans (le_trans
       (le_of_eq (show ‖A‖*(2*(g*x))=2*(g*(‖A‖*x)) from by ring))
       (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hτ (Real.exp_pos _).le) zero_le_two))
  refine ⟨h U,hS,?_⟩
  have hz:= norm_sub_norm_le (bead C d k N p B u z U) (regularRead C d k N p u z U)
  rw [norm_sub_rev] at hz
  have hy : g*(s*v) ≤ s*v:= mul_le_of_le_one_left (mul_nonneg (zero_le_one.trans ha) ((paid_pos ..).trans hb)) hr
  linarith only [hy,hS,hz,h U]

omit H T₀
omit [Fintype J] in
private lemma norm_bound {f g:J→ℂ}(s:Finset J) (b r:ℝ) (h:1≤b) (hr:0≤r)
    (hf:∀ i,‖f i‖ ≤ b) (hg:∀ i,‖g i‖ ≤ b) (hb:∀ i,‖f i-g i‖ ≤ r) :
    ‖(∏ i∈s,f i) - (∏ i∈s,g i)‖ ≤ (s.card:ℝ)*b^s.card*r := by
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert i s hi IH=>
    let x:=∏ j∈s,f j; let y:=∏ j∈s,g j; let a:= b^s.card
    have ha:0≤a:=pow_nonneg (zero_le_one.trans h) _
    have hx: ‖x‖ ≤ a:=by unfold x; rw [norm_prod]; apply (prod_le_prod (fun j _=> norm_nonneg _) (fun j _=> hf j)).trans_eq; exact prod_const _
    rw [prod_insert hi,prod_insert hi]; change ‖f i*x-g i*y‖ ≤ _
    rw [show f i*x-g i*y=(f i-g i)*x+g i*(x-y) from by ring,card_insert_of_notMem hi,pow_succ,Nat.cast_add,Nat.cast_one]; refine (norm_add_le ..).trans ?_
    rw [norm_mul,norm_mul]; apply le_trans (add_le_add (mul_le_mul (hb i) hx (norm_nonneg _) hr) (mul_le_mul (hg i) IH (norm_nonneg _) (zero_le_one.trans h)))
    change r*a+b*(_*a*r)≤ _*(a*b)*r; nlinarith only [mul_le_mul_of_nonneg_right h (mul_nonneg ha hr)] -- fix

variable {φ:Filter I} {u ℓ:I→ℕ} {v s:I→ℝ}
  (L: GracesP C φ u ℓ) {wide:ℕ} (hbig:1≤wide)
variable (hv : Coins φ (C.S.scale ∘ u) v)(hp : ∀ᶠ i in φ,1 ≤ v i)
    (hs : Coins φ (C.S.scale ∘ u) s)(ht : ∀ᶠ i in φ,0<s i)
    (d:J→ℕ)
local notation "b₀" i=> (C.path.levels.budget (u i)).B
local notation "t*" => Fintype.card J
local notation "s*" i => ((C.path.levels.params (u i)).columns*v i)
open GridApprox
include H T₀ L hv hp hs ht
private lemma allRegular :
    ∀ᶠ i in φ, ∀ N p,∀ he:u i < N,∀ x:J→Site (C.side (u i) p), ∀ x₁:(j:J)→ C.label (d j), (∀ j, Spindle.paid C (d j) (u i) N p (x₁ j) ≤ v i) → ∀ s':Finset J, ∀ U, ‖fineJob (fun j=> regularRead C (d j) (u i) N p (x₁ j) (x j)) s' U-fineJob (fun j=> bead C (d j) (u i) N p (b₀ i) (x₁ j) (x j)) s' U‖ ≤ s i := by
    let Y i := s* i; let q i:=5*Y i; let a i:= (t*:ℝ)*q i^t* * (2*Y i)/s i
    let lo:= C.S.scale ∘ u; have hz:= C.S.divergent.comp L.seeks
    have hY: Cheap φ lo Y := Cheap.mul (columns_p hz H.cuts.toPackage.toTableTickets L.ages|>.up) hv.up
    have ha: Cheap φ lo a := Cheap.div (Cheap.mul (Cheap.mul (Bill.const _ hz) (Cheap.power (Cheap.mul (Bill.const _ hz) hY) hz t*)) (Cheap.mul (Bill.const _ hz) hY)) hs
    filter_upwards [stainBeat H L ha,hp,ht,eventually_all.mpr (fun j=> L.seeks.eventually_ge_atTop (C.ref (d j))), L.seeks.eventually_gt_atTop (C.ref 0)] with i hS hb hf hl hm N p he x x₁ hD s' U
    have hyy:1 ≤ Y i:= one_le_mul_of_one_le_of_one_le (C.path.levels.params _|>.columns_ge) hb
    let t:= Real.exp (-(2:ℝ)*(b₀ i:ℝ)); have ht':0<t:= Real.exp_pos _
    have h(j):=enamelCost H T₀ (x j) (hl j) hm he (x₁ j) (hD j)
    have hr := norm_bound s' (q i) (2*(t * Y i)) (by unfold q; linarith only [hyy]) (by positivity) (fun j=> ((h j).2.2 U).1.trans (show 3*(Y i)≤ _ from by unfold q; linarith only [hyy])) (fun j=>(h j).2.2 U|>.2.2) (fun j=>(h j).2.2 U|>.2.1)
    apply hr.trans; apply (mul_le_mul_of_nonneg_right (mul_le_mul (by exact_mod_cast card_le_univ s' : (s'.card:ℝ)≤t*) (pow_le_pow_right₀ (show 1 ≤ q i by unfold q; linarith only [hyy]) (card_le_univ ..)) (by unfold q; positivity) (Nat.cast_nonneg _)) (show 0≤2*(t * Y i) by positivity)).trans
    have hh: a i * t ≤ 1 := (mul_le_mul_of_nonneg_right (Real.le_norm_self _) ht'.le).trans hS.2
    refine le_trans (le_of_eq (show _ = a i*t * s i from ?_)) ((mul_le_mul_of_nonneg_right hh hf.le).trans_eq (one_mul _)); unfold a; field_simp

include hbig
lemma columnLaw : ∀ᶠ i in φ, ∀ N p,∀ he:u i < N,∀ x:J→Site (C.side (u i) p), (∀ k j,separation (x k) (x j) ≤ wide*ℓ i) → (∀ k j,k≠j → ℓ i≤ separation (x k) (x j)) → ∀ x₁:(j:J)→ C.label (d j), (∀ j, Spindle.paid C (d j) (u i) N p (x₁ j) ≤ v i) → ∀ s':Finset J, ‖moment (C.beta N p) (fineJob (fun j=>abrade C (x₁ j) N (u i) p (x j) he.le) s') - ∫ U, fineJob (fun j=> regularRead C (d j) (u i) N p (x₁ j) (x j)) s' U ∂(Therm.scene C.path N p (u i))‖ ≤ s i :=by
   let t i:= s i/2; let hT:= C.S.divergent.comp L.seeks; have hc: Coins φ (C.S.scale ∘ u) t:= Coins.div hs (Bi.const _ (by norm_num) hT); have ht':∀ᶠ i in φ,0<t i:= ht.mono fun i hi=> half_pos hi
   filter_upwards [overBoard H L T₀ hbig hv hp hc ht' d,allRegular H T₀ L hv hp hc ht' d,eventually_all.mpr (fun j=> L.seeks.eventually_ge_atTop (C.ref (d j))), L.seeks.eventually_gt_atTop (C.ref 0)] with i hx hy hl hm N p he x hG hF x₁ hW s'
   let Y:= fineJob (fun j=> regularRead C (d j) (u i) N p (x₁ j) (x j)) s'; let y:= fineJob (fun j=> bead C (d j) (u i) N p (b₀ i) (x₁ j) (x j)) s'
   let V:= Therm.scene C.path N p (u i); letI : IsProbabilityMeasure V:= Therm.probability H.seed.wilson he.le
   let μ(f:Config G (C.side (u i) p)→ℂ):= ∫ U,f U∂V
   have hA:= hx N p he x hG hF x₁ hW s'
   have h(j):= enamelCost H T₀ (x j) (hl j) hm he (x₁ j) (hW j)
   let M := moment (C.beta N p) (fineJob (fun j=>abrade C (x₁ j) N (u i) p (x j) he.le) s')
   have hb: ‖μ y-μ Y‖ ≤ t i:=by
       have hx : Integrable Y V:= (Envelope.prodC s' _ (fun i _=>(h i).1)).integrableC V
       have hy' : Integrable y V:= (Envelope.prodC s' _ (fun i _=>(h i).2.1)).integrableC V
       unfold μ; rw [norm_sub_rev,← MeasureTheory.integral_sub hx hy']; refine (norm_integral_le_integral_norm _).trans ((MeasureTheory.integral_mono (hx.sub hy').norm (integrable_const (t i)) ?_).trans_eq (by simp))
       exact fun U=> hy N p he x x₁ hW s' U
   change ‖M-μ Y‖≤ _; rw [show M-μ Y=M-μ y+(μ y-μ Y) from by abel]; exact (norm_add_le ..).trans ((add_le_add hA hb).trans_eq (by unfold t; ring))
end YM.OPE.Strobe.Panoramic
