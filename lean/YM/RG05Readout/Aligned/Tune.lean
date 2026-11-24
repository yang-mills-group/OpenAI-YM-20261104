import YM.MergeProof.South.Merman
import YM.OPE.Portfolio.Billing
import YM.RG05Readout.Aligned.Columns

/-!
# Reading from actual labelled capture, retaining the constructing path

For use in real comparison in `Aligned`. Given the ACTUAL output density,
choose one representation with prices and a certified (nonanalytic) step
continuation to the `ref` of the literal-point prescription. Read using
the construction's actual linear readout maps, **not** tuning by comparing
the unknown correlations. No conclusion here that this coordinate is exactly
representation independent (address/mask/wrapping as usual).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Aligned
open Function Filter Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Exponential MergeProof
open Accent Ribbons.ManyCopies.Cadet.Studio Relay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge} {C:Family G} {N k m p d:ℕ}
    {u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    {W : Worth}
set_option quotPrecheck false
local notation "R"=> C.path.rep N p
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "s!"=> C.factory d N p
variable {M:Extra.Histories.Music (C.labels.level d) C.path N p}

/-- The columns and transfer maps are *literally from this Family*. -/
structure Committed (C:Family G) (N p d : ℕ) (W:Worth) (ψ:ℕ→ℝ)
    (D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))
    (M:Extra.Histories.Music (C.labels.level d) C.path N p) : Prop where
    origin : (C.factory d N p).entries=(M.draft C.path).inits
    sessions : Sessions (C.localSection d) M (C.ref d) C.params W ψ D
    reborn x : profile (C.path.rep N p N).activities ((M.tone N).plays x).forced=
        hook (C.path.rep N p N).activities (C.path.rep N p N).p.threshold
          (booster (C.localSection d) (C.path.rep N p N) 0 x)

lemma committing (h:Scrim C W u ψ φ δ ζ r D) (hi:C.ref d ≤ N) :
    ∃ M, Committed C N p d W ψ D M := by
    obtain ⟨Z,hx,hZ,hp,hk⟩:= (h.costs.aim d N p hi).lyrics
    exact ⟨Z,hx,⟨hZ,hp,h.listens d N p,h.costs.cost,h.costs.back⟩,hk⟩

variable (H:Committed C N p d W ψ D M) {Z: Coefficient (C.labels.level d) (C.side k p)}
    {t E:ℝ}
    {A:∀ i:ℕ,Relay.Solo (C.labels.level d) C.path p i}

/-- Any match with this transcript. Relational in order not to impose a
false uniqueness of `a` under re-expression. Its coordinate is read below
from the transcript, and the cost estimates here are *uniform* on these
choices. -/
structure Pickup (C:Family G)(M:Extra.Histories.Music (C.labels.level d) C.path N p)
    (ψ:ℕ→ℝ) (D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))
    (H:Committed C N p d W ψ D M)
    (k:ℕ) (Z:Coefficient (C.labels.level d) (C.side k p))(t E:ℝ)
    (A:∀ i:ℕ,Relay.Solo (C.labels.level d) C.path p i) : Prop where
    top : k≤N
    admissible : C.ref d ≤ k
    opens : Z.Format 0 C.params (C.path.rep N p k)
    funds : Z.remBound 0 (C.path.rep N p k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) t
    starts : A k=Relay.pair C.path N p M Z t
    traces : Challenge (C.localSection d) C.path N p C.params W M (C.ref d) k A
    logged (i:ℕ) (_he:C.ref d ≤ i)(hi:i<k):
      Accord (C.localSection d) C.path N p M (ψ i) i (D N p i (hi.trans_le top)) (A (i+1)) (A i)
    expenses : let P:=dualize C.path N p M (C.ref d) k A (-(A (C.ref d)).a); ∀ i:ℕ,(C.ref d) ≤ i → i ≤ k →
        gainChart C.path k i*(P.cost i+(C.labels.level d).coeffSize (P.voice i).x) ≤ E
    size : (C.labels.level d).coeffSize Z.x ≤ E

lemma picks (h:C.Makes) (hk:C.ref d ≤ k)(hi:k ≤ N)(hr:Z.Format 0 C.params (R k))
    (hv:Z.remBound 0 (R k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) t)(x:ℝ)
    (hx:(F).coeffSize Z.x+t ≤ x)(hp:4*(1+(C.path.levels.params k).columns)*x ≤ E) :
    ∃ A, Pickup C M ψ D H k Z t E A := by
    let HT := H.sessions
    obtain ⟨A,hK,hX,hY,_,_,_,hE⟩:= antilles Y! T N p C.params W M (D N p) ψ le_rfl hk hi h.wilson HT.sung
      (fun j hj hu=>⟨HT.stamps j hj _, HT.songs j hj _⟩) Z hr hv hx HT.credit HT.brine
    refine ⟨A,hi,hk,hr,hv,hK,hX,hY, fun i hi hz=> (hE i hi hz).trans hp,?_⟩
    have h₁ : (F).coeffSize Z.x ≤ x := (le_add_of_nonneg_right (rem_nonneg hv)).trans hx
    have h₂ := (C.path.levels.params k).columns_ge
    exact h₁.trans ((le_mul_of_one_le_left ((Work.G08.size_nonneg ..).trans h₁) (by linarith only [h₂])).trans hp)

variable {H}
namespace Pickup
variable (h: Pickup C M ψ D H k Z t E A)
include h

/-- Full transmission as a single insertion, *inserting also the
compensation* with this very Music. -/
lemma transfer (i:ℕ)(hm:ℓ ≤ i)(hi:i<k) v :
      ((A i).bar M v).density 0 Y! (R i)=
        blast T N p i d (((A (i+1)).bar M v).density 0 Y! (R (i+1))):=
    (h.traces.ships i hm hi).debt v

lemma value (hC:C.Makes) :
      ((A k).bar M 0).density 0 Y! (R k)=Z.density 0 Y! (R k) := by
    have hX:=H.sessions.sung.earned k h.admissible h.top
    have hf: ((M.tone k).plays 0).density 0 Y! (R k)=0:=
       map_zero (IsLinearMap.mk' _ hX.values)
    have hx:=((originate Y! T N p C.params M h.top hC.wilson hX h.opens h.funds (le_refl ((F).coeffSize Z.x+t))).2 0).2.1
    rw [h.starts,hx,hf,add_zero]

lemma ref_coordinate (hC:C.Makes) : ((A ℓ).bar M 0).x=
    (s!).terminal (A ℓ).a:= by
    have ht:=h.admissible.trans h.top
    rw [(keys Y! T N p C.params M _ (h.traces.chairs ℓ le_rfl h.admissible)
          (H.sessions.sung.earned ℓ le_rfl ht)).1,add_zero,
        ← (hC.calibrated d N p ht).reads,H.origin]
    exact ((H.sessions.sung.earned ℓ le_rfl ht).currents _).symm

/-- Pointer goes BACK onto the actual columns at m (observation), in this
aligned, threshold-unit prescription. -/
def coordinate (M:Extra.Histories.Music (C.labels.level d) C.path N p) (A:∀ i:ℕ,Relay.Solo (C.labels.level d) C.path p i) (m:ℕ) (hC:C.Makes) : C.label d :=
    (((C.S.a m:ℂ)^d)⁻¹) • Charts.window C hC d m N p ((A ℓ).bar M 0).x

lemma scale_back (m:ℕ)(hC:C.Makes) : masterRef hC d m N p (coordinate M A m hC)=
    (s!).terminal (A ℓ).a := by
     rw [← h.ref_coordinate hC]
     let Q := Charts.window C hC d m N p; let w:=(C.S.a m:ℂ)^d
     let x:= ((A ℓ).bar M 0).x
     change w • Q.symm (w⁻¹ • Q x)=x
     rw [map_smul,ContinuousLinearEquiv.symm_apply_apply,smul_smul,
         mul_inv_cancel₀ (show w≠0 from pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')),one_smul]

lemma size_bound (hC:C.Makes) : (F).coeffSize ((M.tone k).index (A ℓ).a) ≤ 2*E := by
    let x:= (A ℓ).a
    let V:= (A k).bar M (-x)
    have hr := h.expenses k h.admissible le_rfl
    rw [gainChart,sub_self,mul_zero,Real.exp_zero,one_mul] at hr
    have hz : (F).coeffSize V.x ≤ E:=
       (le_add_of_nonneg_left (rem_nonneg ((keys Y! T N p C.params M (-x) (h.traces.chairs _ h.admissible le_rfl)
         (H.sessions.sung.earned _ h.admissible h.top)).2.2))).trans hr
    have hx : V.x=Z.x+ (M.tone k).index (-x) := by
       unfold V
       rw [h.starts]
       exact ((originate Y! T N p C.params M h.top hC.wilson (H.sessions.sung.earned _ h.admissible h.top) h.opens h.funds (le_refl ((F).coeffSize Z.x+t))).2 _).1
    rw [map_neg, ← sub_eq_add_neg] at hx
    rw [show (M.tone k).index (A ℓ).a= Z.x + - V.x from by rw [hx]; unfold x; abel, two_mul]; apply (Size.add ..).trans
    exact add_le_add h.size (by simpa only [Labels.Frame.coeffSize, Pi.neg_apply, norm_neg] using hz)

/-- Reissue with SIGNED compensation and unchanged selected path. Charges
for carrying the compensated difference after matching. -/
lemma declare (U: Scrim C W u ψ φ δ ζ r D) (w:ℝ)(hw:0 < w)(hb:ℓ ≤ m)(hm:m ≤ k)
   (hQ:w*‖alto T m d‖*(E/gainChart T k m) ≤ ζ d m/2):
   let P:=dualize T N p M ℓ k A (-(A ℓ).a)
   Club T C.params Y! (ζ d) ψ m k N p (fun i=> march (fun _:Unit=>w) φ m i ()) D P.voice P.cost h.top := by
     let hv:=diet T d m φ (fun i=>ζ d i/2) w hw (fun i _=> (U.costs.stay.water i (Nat.zero_le i)).1)
       (fun i he=> le_trans (le_of_eq (b:=(φ i * ((C.S.block i).val:ℝ)^(d+1)* ζ d i)/2)
          (by ring)) (div_le_div_of_nonneg_right (U.jump d i (hb.trans he)) (by norm_num))) k E
       ((Work.G08.size_nonneg ..).trans h.size) hQ
     intro P
     exact Sessions.reissue Y! H.sessions h.admissible h.top hb hm h.traces h.logged
        (t':=fun i=> E/gainChart T k i) (fun i hi ht=> (le_div_iff₀ (Real.exp_pos _)).mpr ((mul_comm ..).trans_le (h.expenses i (hb.trans hi) ht)))
        (fun i hi ht=> (hv i hi).trans (div_le_self (U.grows d i (hb.trans hi)|>.le) (by norm_num)))
        (fun i hi ht=> by
           have h0 : Brine T m δ φ:=⟨fun i _=> U.costs.stay.water _ (Nat.zero_le i), fun i _=> U.costs.stay.mint _ (Nat.zero_le i), fun i _=> U.costs.stay.split _ (Nat.zero_le i), fun i _=> U.costs.stay.support _ (Nat.zero_le i)⟩
           exact (march_pos _ _ _ _ _ (fun _=>hw) h0 i hi _).le)

end Pickup
end YM.RG05Readout.Aligned
